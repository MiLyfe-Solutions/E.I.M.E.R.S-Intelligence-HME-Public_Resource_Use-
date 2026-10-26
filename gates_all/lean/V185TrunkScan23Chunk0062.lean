import V185TrunkScan23Chunk0061

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_366248 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_366248 : Nat := 118140960795 + 366248 * 2 ^ 59
def prefixEnd_366248 : Nat := 4983230072969 + 3 ^ 40 * 366248 * 2
def baseEnd_366248 : Nat := 188061262747988286715663

theorem tailTrace_366248 : CollatzResearch.WordTrace tailWord_366248 prefixEnd_366248 188061262747988286715663 := by
  unfold tailWord_366248
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679080988576760511817699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8905441318102347349090265 6679080988576760511817699)
  ·
    refine ⟨10018621482865140767726549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679080988576760511817699 10018621482865140767726549)
    ·
      refine ⟨234811441004651736743591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10018621482865140767726549 234811441004651736743591)
      ·
        refine ⟨352217161506977605115387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234811441004651736743591 352217161506977605115387)
        ·
          refine ⟨528325742260466407673081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352217161506977605115387 528325742260466407673081)
          ·
            refine ⟨396244306695349805754811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528325742260466407673081 396244306695349805754811)
            ·
              refine ⟨594366460043024708632217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396244306695349805754811 594366460043024708632217)
              ·
                refine ⟨445774845032268531474163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594366460043024708632217 445774845032268531474163)
                ·
                  refine ⟨668662267548402797211245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445774845032268531474163 668662267548402797211245)
                  ·
                    refine ⟨250748350330651048954217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 668662267548402797211245 250748350330651048954217)
                    ·
                      refine ⟨188061262747988286715663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250748350330651048954217 188061262747988286715663)
                      ·
                        rfl

theorem cell23_366248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_366248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366248 prefixEnd_366248 := by exact prefixLift 366248
  have htrace : WordTrace (prefixWord ++ tailWord_366248) baseStart_366248 baseEnd_366248 := by
    simpa [prefixWord, tailWord_366248, baseEnd_366248] using wordTrace_append hprefix tailTrace_366248
  have hstable : (prefixWord ++ tailWord_366248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366248).length < 2 ^ (prefixWord ++ tailWord_366248).sum := by decide
  have hdescent : baseEnd_366248 < baseStart_366248 := by decide
  rcases family_descends (prefixWord ++ tailWord_366248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366263 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 2, 5]
def baseStart_366263 : Nat := 118140960795 + 366263 * 2 ^ 59
def prefixEnd_366263 : Nat := 4983230072969 + 3 ^ 40 * 366263 * 2
def baseEnd_366263 : Nat := 62689654985935242676031

theorem tailTrace_366263 : CollatzResearch.WordTrace tailWord_366263 prefixEnd_366263 62689654985935242676031 := by
  unfold tailWord_366263
  simp only [CollatzResearch.WordTrace]
  refine ⟨13358709072099178585431443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8905806048066119056954295 13358709072099178585431443)
  ·
    refine ⟨20038063608148767878147165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13358709072099178585431443 20038063608148767878147165)
    ·
      refine ⟨7514273853055787954305187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20038063608148767878147165 7514273853055787954305187)
      ·
        refine ⟨11271410779583681931457781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7514273853055787954305187 11271410779583681931457781)
        ·
          refine ⟨1056694760585970181074167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11271410779583681931457781 1056694760585970181074167)
          ·
            refine ⟨1585042140878955271611251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056694760585970181074167 1585042140878955271611251)
            ·
              refine ⟨2377563211318432907416877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585042140878955271611251 2377563211318432907416877)
              ·
                refine ⟨891586204244412340281329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2377563211318432907416877 891586204244412340281329)
                ·
                  refine ⟨668689653183309255210997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 891586204244412340281329 668689653183309255210997)
                  ·
                    refine ⟨62689654985935242676031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 668689653183309255210997 62689654985935242676031)
                    ·
                      rfl

theorem cell23_366263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_366263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366263 prefixEnd_366263 := by exact prefixLift 366263
  have htrace : WordTrace (prefixWord ++ tailWord_366263) baseStart_366263 baseEnd_366263 := by
    simpa [prefixWord, tailWord_366263, baseEnd_366263] using wordTrace_append hprefix tailTrace_366263
  have hstable : (prefixWord ++ tailWord_366263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366263).length < 2 ^ (prefixWord ++ tailWord_366263).sum := by decide
  have hdescent : baseEnd_366263 < baseStart_366263 := by decide
  rcases family_descends (prefixWord ++ tailWord_366263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366278 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_366278 : Nat := 118140960795 + 366278 * 2 ^ 59
def prefixEnd_366278 : Nat := 4983230072969 + 3 ^ 40 * 366278 * 2
def baseEnd_366278 : Nat := 188076667167623169340525

theorem tailTrace_366278 : CollatzResearch.WordTrace tailWord_366278 prefixEnd_366278 188076667167623169340525 := by
  unfold tailWord_366278
  simp only [CollatzResearch.WordTrace]
  refine ⟨417476755220151129600859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8906170778029890764818325 417476755220151129600859)
  ·
    refine ⟨626215132830226694401289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 417476755220151129600859 626215132830226694401289)
    ·
      refine ⟨469661349622670020800967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626215132830226694401289 469661349622670020800967)
      ·
        refine ⟨704492024434005031201451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469661349622670020800967 704492024434005031201451)
        ·
          refine ⟨1056738036651007546802177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704492024434005031201451 1056738036651007546802177)
          ·
            refine ⟨792553527488255660101633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056738036651007546802177 792553527488255660101633)
            ·
              refine ⟨594415145616191745076225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792553527488255660101633 594415145616191745076225)
              ·
                refine ⟨445811359212143808807169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594415145616191745076225 445811359212143808807169)
                ·
                  refine ⟨334358519409107856605377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445811359212143808807169 334358519409107856605377)
                  ·
                    refine ⟨250768889556830892454033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334358519409107856605377 250768889556830892454033)
                    ·
                      refine ⟨188076667167623169340525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250768889556830892454033 188076667167623169340525)
                      ·
                        rfl

theorem cell23_366278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_366278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366278 prefixEnd_366278 := by exact prefixLift 366278
  have htrace : WordTrace (prefixWord ++ tailWord_366278) baseStart_366278 baseEnd_366278 := by
    simpa [prefixWord, tailWord_366278, baseEnd_366278] using wordTrace_append hprefix tailTrace_366278
  have hstable : (prefixWord ++ tailWord_366278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366278).length < 2 ^ (prefixWord ++ tailWord_366278).sum := by decide
  have hdescent : baseEnd_366278 < baseStart_366278 := by decide
  rcases family_descends (prefixWord ++ tailWord_366278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366283 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 3, 6, 2]
def baseStart_366283 : Nat := 118140960795 + 366283 * 2 ^ 59
def prefixEnd_366283 : Nat := 4983230072969 + 3 ^ 40 * 366283 * 2
def baseEnd_366283 : Nat := 188079234570895649778001

theorem tailTrace_366283 : CollatzResearch.WordTrace tailWord_366283 prefixEnd_366283 188079234570895649778001 := by
  unfold tailWord_366283
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359438532026722001159503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8906292354684481334106335 13359438532026722001159503)
  ·
    refine ⟨20039157798040083001739255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13359438532026722001159503 20039157798040083001739255)
    ·
      refine ⟨30058736697060124502608883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20039157798040083001739255 30058736697060124502608883)
      ·
        refine ⟨45088105045590186753913325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30058736697060124502608883 45088105045590186753913325)
        ·
          refine ⟨16908039392096320032717497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45088105045590186753913325 16908039392096320032717497)
          ·
            refine ⟨12681029544072240024538123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16908039392096320032717497 12681029544072240024538123)
            ·
              refine ⟨19021544316108360036807185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12681029544072240024538123 19021544316108360036807185)
              ·
                refine ⟨14266158237081270027605389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19021544316108360036807185 14266158237081270027605389)
                ·
                  refine ⟨5349809338905476260352021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14266158237081270027605389 5349809338905476260352021)
                  ·
                    refine ⟨250772312761194199704001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5349809338905476260352021 250772312761194199704001)
                    ·
                      refine ⟨188079234570895649778001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250772312761194199704001 188079234570895649778001)
                      ·
                        rfl

theorem cell23_366283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 6, 2].length) (baseStart_366283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366283 prefixEnd_366283 := by exact prefixLift 366283
  have htrace : WordTrace (prefixWord ++ tailWord_366283) baseStart_366283 baseEnd_366283 := by
    simpa [prefixWord, tailWord_366283, baseEnd_366283] using wordTrace_append hprefix tailTrace_366283
  have hstable : (prefixWord ++ tailWord_366283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366283).length < 2 ^ (prefixWord ++ tailWord_366283).sum := by decide
  have hdescent : baseEnd_366283 < baseStart_366283 := by decide
  rcases family_descends (prefixWord ++ tailWord_366283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366284 : List Nat := [2, 2, 1, 5, 2, 2, 2, 2, 5]
def baseStart_366284 : Nat := 118140960795 + 366284 * 2 ^ 59
def prefixEnd_366284 : Nat := 4983230072969 + 3 ^ 40 * 366284 * 2
def baseEnd_366284 : Nat := 20897749783505571762833

theorem tailTrace_366284 : CollatzResearch.WordTrace tailWord_366284 prefixEnd_366284 20897749783505571762833 := by
  unfold tailWord_366284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679737502511549585972953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8906316670015399447963937 6679737502511549585972953)
  ·
    refine ⟨5009803126883662189479715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6679737502511549585972953 5009803126883662189479715)
    ·
      refine ⟨7514704690325493284219573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5009803126883662189479715 7514704690325493284219573)
      ·
        refine ⟨704503564718014995395585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7514704690325493284219573 704503564718014995395585)
        ·
          refine ⟨528377673538511246546689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704503564718014995395585 528377673538511246546689)
          ·
            refine ⟨396283255153883434910017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528377673538511246546689 396283255153883434910017)
            ·
              refine ⟨297212441365412576182513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396283255153883434910017 297212441365412576182513)
              ·
                refine ⟨222909331024059432136885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297212441365412576182513 222909331024059432136885)
                ·
                  refine ⟨20897749783505571762833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 222909331024059432136885 20897749783505571762833)
                  ·
                    rfl

theorem cell23_366284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_366284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366284 prefixEnd_366284 := by exact prefixLift 366284
  have htrace : WordTrace (prefixWord ++ tailWord_366284) baseStart_366284 baseEnd_366284 := by
    simpa [prefixWord, tailWord_366284, baseEnd_366284] using wordTrace_append hprefix tailTrace_366284
  have hstable : (prefixWord ++ tailWord_366284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366284).length < 2 ^ (prefixWord ++ tailWord_366284).sum := by decide
  have hdescent : baseEnd_366284 < baseStart_366284 := by decide
  rcases family_descends (prefixWord ++ tailWord_366284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366294 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_366294 : Nat := 118140960795 + 366294 * 2 ^ 59
def prefixEnd_366294 : Nat := 4983230072969 + 3 ^ 40 * 366294 * 2
def baseEnd_366294 : Nat := 188084882858095106740451

theorem tailTrace_366294 : CollatzResearch.WordTrace tailWord_366294 prefixEnd_366294 188084882858095106740451 := by
  unfold tailWord_366294
  simp only [CollatzResearch.WordTrace]
  refine ⟨834989983436679429988121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8906559823324580586539957 834989983436679429988121)
  ·
    refine ⟨626242487577509572491091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 834989983436679429988121 626242487577509572491091)
    ·
      refine ⟨939363731366264358736637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 626242487577509572491091 939363731366264358736637)
      ·
        refine ⟨352261399262349134526239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 939363731366264358736637 352261399262349134526239)
        ·
          refine ⟨528392098893523701789359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352261399262349134526239 528392098893523701789359)
          ·
            refine ⟨792588148340285552684039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528392098893523701789359 792588148340285552684039)
            ·
              refine ⟨1188882222510428329026059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792588148340285552684039 1188882222510428329026059)
              ·
                refine ⟨1783323333765642493539089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188882222510428329026059 1783323333765642493539089)
                ·
                  refine ⟨1337492500324231870154317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1783323333765642493539089 1337492500324231870154317)
                  ·
                    refine ⟨501559687621586951307869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1337492500324231870154317 501559687621586951307869)
                    ·
                      refine ⟨188084882858095106740451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501559687621586951307869 188084882858095106740451)
                      ·
                        rfl

theorem cell23_366294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_366294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366294 prefixEnd_366294 := by exact prefixLift 366294
  have htrace : WordTrace (prefixWord ++ tailWord_366294) baseStart_366294 baseEnd_366294 := by
    simpa [prefixWord, tailWord_366294, baseEnd_366294] using wordTrace_append hprefix tailTrace_366294
  have hstable : (prefixWord ++ tailWord_366294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366294).length < 2 ^ (prefixWord ++ tailWord_366294).sum := by decide
  have hdescent : baseEnd_366294 < baseStart_366294 := by decide
  rcases family_descends (prefixWord ++ tailWord_366294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366303 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 3]
def baseStart_366303 : Nat := 118140960795 + 366303 * 2 ^ 59
def prefixEnd_366303 : Nat := 4983230072969 + 3 ^ 40 * 366303 * 2
def baseEnd_366303 : Nat := 188089504183985571527909

theorem tailTrace_366303 : CollatzResearch.WordTrace tailWord_366303 prefixEnd_366303 188089504183985571527909 := by
  unfold tailWord_366303
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360167991954265416887563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8906778661302843611258375 13360167991954265416887563)
  ·
    refine ⟨20040251987931398125331345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13360167991954265416887563 20040251987931398125331345)
    ·
      refine ⟨15030188990948548593998509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20040251987931398125331345 15030188990948548593998509)
      ·
        refine ⟨5636320871605705722749441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15030188990948548593998509 5636320871605705722749441)
        ·
          refine ⟨4227240653704279292062081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5636320871605705722749441 4227240653704279292062081)
          ·
            refine ⟨3170430490278209469046561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4227240653704279292062081 3170430490278209469046561)
            ·
              refine ⟨2377822867708657101784921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3170430490278209469046561 2377822867708657101784921)
              ·
                refine ⟨1783367150781492826338691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2377822867708657101784921 1783367150781492826338691)
                ·
                  refine ⟨2675050726172239239508037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783367150781492826338691 2675050726172239239508037)
                  ·
                    refine ⟨501572011157294857407757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2675050726172239239508037 501572011157294857407757)
                    ·
                      refine ⟨188089504183985571527909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501572011157294857407757 188089504183985571527909)
                      ·
                        rfl

theorem cell23_366303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_366303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366303 prefixEnd_366303 := by exact prefixLift 366303
  have htrace : WordTrace (prefixWord ++ tailWord_366303) baseStart_366303 baseEnd_366303 := by
    simpa [prefixWord, tailWord_366303, baseEnd_366303] using wordTrace_append hprefix tailTrace_366303
  have hstable : (prefixWord ++ tailWord_366303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366303).length < 2 ^ (prefixWord ++ tailWord_366303).sum := by decide
  have hdescent : baseEnd_366303 < baseStart_366303 := by decide
  rcases family_descends (prefixWord ++ tailWord_366303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366317 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_366317 : Nat := 118140960795 + 366317 * 2 ^ 59
def prefixEnd_366317 : Nat := 4983230072969 + 3 ^ 40 * 366317 * 2
def baseEnd_366317 : Nat := 188096692913148516752845

theorem tailTrace_366317 : CollatzResearch.WordTrace tailWord_366317 prefixEnd_366317 188096692913148516752845 := by
  unfold tailWord_366317
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360678613903545807897205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8907119075935697205264803 13360678613903545807897205)
  ·
    refine ⟨1252563620053457419490363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13360678613903545807897205 1252563620053457419490363)
    ·
      refine ⟨1878845430080186129235545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252563620053457419490363 1878845430080186129235545)
      ·
        refine ⟨1409134072560139596926659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878845430080186129235545 1409134072560139596926659)
        ·
          refine ⟨2113701108840209395389989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409134072560139596926659 2113701108840209395389989)
          ·
            refine ⟨396318957907539261635623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2113701108840209395389989 396318957907539261635623)
            ·
              refine ⟨594478436861308892453435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396318957907539261635623 594478436861308892453435)
              ·
                refine ⟨891717655291963338680153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594478436861308892453435 891717655291963338680153)
                ·
                  refine ⟨668788241468972504010115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 891717655291963338680153 668788241468972504010115)
                  ·
                    refine ⟨1003182362203458756015173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 668788241468972504010115 1003182362203458756015173)
                    ·
                      refine ⟨188096692913148516752845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1003182362203458756015173 188096692913148516752845)
                      ·
                        rfl

theorem cell23_366317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_366317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366317 prefixEnd_366317 := by exact prefixLift 366317
  have htrace : WordTrace (prefixWord ++ tailWord_366317) baseStart_366317 baseEnd_366317 := by
    simpa [prefixWord, tailWord_366317, baseEnd_366317] using wordTrace_append hprefix tailTrace_366317
  have hstable : (prefixWord ++ tailWord_366317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366317).length < 2 ^ (prefixWord ++ tailWord_366317).sum := by decide
  have hdescent : baseEnd_366317 < baseStart_366317 := by decide
  rcases family_descends (prefixWord ++ tailWord_366317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366340 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 6]
def baseStart_366340 : Nat := 118140960795 + 366340 * 2 ^ 59
def prefixEnd_366340 : Nat := 4983230072969 + 3 ^ 40 * 366340 * 2
def baseEnd_366340 : Nat := 20900944774244658529471

theorem tailTrace_366340 : CollatzResearch.WordTrace tailWord_366340 prefixEnd_366340 20900944774244658529471 := by
  unfold tailWord_366340
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680758746410110367992237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8907678328546813823989649 6680758746410110367992237)
  ·
    refine ⟨2505284529903791387997089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6680758746410110367992237 2505284529903791387997089)
    ·
      refine ⟨1878963397427843540997817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2505284529903791387997089 1878963397427843540997817)
      ·
        refine ⟨1409222548070882655748363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1878963397427843540997817 1409222548070882655748363)
        ·
          refine ⟨2113833822106323983622545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409222548070882655748363 2113833822106323983622545)
          ·
            refine ⟨1585375366579742987716909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113833822106323983622545 1585375366579742987716909)
            ·
              refine ⟨594515762467403620393841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1585375366579742987716909 594515762467403620393841)
              ·
                refine ⟨445886821850552715295381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594515762467403620393841 445886821850552715295381)
                ·
                  refine ⟨20900944774244658529471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 445886821850552715295381 20900944774244658529471)
                  ·
                    rfl

theorem cell23_366340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_366340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366340 prefixEnd_366340 := by exact prefixLift 366340
  have htrace : WordTrace (prefixWord ++ tailWord_366340) baseStart_366340 baseEnd_366340 := by
    simpa [prefixWord, tailWord_366340, baseEnd_366340] using wordTrace_append hprefix tailTrace_366340
  have hstable : (prefixWord ++ tailWord_366340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366340).length < 2 ^ (prefixWord ++ tailWord_366340).sum := by decide
  have hdescent : baseEnd_366340 < baseStart_366340 := by decide
  rcases family_descends (prefixWord ++ tailWord_366340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366360 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 1, 5, 2]
def baseStart_366360 : Nat := 118140960795 + 366360 * 2 ^ 59
def prefixEnd_366360 : Nat := 4983230072969 + 3 ^ 40 * 366360 * 2
def baseEnd_366360 : Nat := 188118772581291848515147

theorem tailTrace_366360 : CollatzResearch.WordTrace tailWord_366360 prefixEnd_366360 188118772581291848515147 := by
  unfold tailWord_366360
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681123476373882075856267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8908164635165176101141689 6681123476373882075856267)
  ·
    refine ⟨10021685214560823113784401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6681123476373882075856267 10021685214560823113784401)
    ·
      refine ⟨7516263910920617335338301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10021685214560823113784401 7516263910920617335338301)
      ·
        refine ⟨2818598966595231500751863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7516263910920617335338301 2818598966595231500751863)
        ·
          refine ⟨4227898449892847251127795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818598966595231500751863 4227898449892847251127795)
          ·
            refine ⟨6341847674839270876691693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227898449892847251127795 6341847674839270876691693)
            ·
              refine ⟨2378192878064726578759385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6341847674839270876691693 2378192878064726578759385)
              ·
                refine ⟨1783644658548544934069539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378192878064726578759385 1783644658548544934069539)
                ·
                  refine ⟨2675466987822817401104309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783644658548544934069539 2675466987822817401104309)
                  ·
                    refine ⟨250825030108389131353529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2675466987822817401104309 250825030108389131353529)
                    ·
                      refine ⟨188118772581291848515147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250825030108389131353529 188118772581291848515147)
                      ·
                        rfl

theorem cell23_366360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_366360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366360 prefixEnd_366360 := by exact prefixLift 366360
  have htrace : WordTrace (prefixWord ++ tailWord_366360) baseStart_366360 baseEnd_366360 := by
    simpa [prefixWord, tailWord_366360, baseEnd_366360] using wordTrace_append hprefix tailTrace_366360
  have hstable : (prefixWord ++ tailWord_366360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366360).length < 2 ^ (prefixWord ++ tailWord_366360).sum := by decide
  have hdescent : baseEnd_366360 < baseStart_366360 := by decide
  rcases family_descends (prefixWord ++ tailWord_366360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366403 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6]
def baseStart_366403 : Nat := 118140960795 + 366403 * 2 ^ 59
def prefixEnd_366403 : Nat := 4983230072969 + 3 ^ 40 * 366403 * 2
def baseEnd_366403 : Nat := 188140852249435180277449

theorem tailTrace_366403 : CollatzResearch.WordTrace tailWord_366403 prefixEnd_366403 188140852249435180277449 := by
  unfold tailWord_366403
  simp only [CollatzResearch.WordTrace]
  refine ⟨13363815291591982495527863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8909210194394654997018575 13363815291591982495527863)
  ·
    refine ⟨20045722937387973743291795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13363815291591982495527863 20045722937387973743291795)
    ·
      refine ⟨30068584406081960614937693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20045722937387973743291795 30068584406081960614937693)
      ·
        refine ⟨11275719152280735230601635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30068584406081960614937693 11275719152280735230601635)
        ·
          refine ⟨16913578728421102845902453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11275719152280735230601635 16913578728421102845902453)
          ·
            refine ⟨1585648005789478391803355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16913578728421102845902453 1585648005789478391803355)
            ·
              refine ⟨2378472008684217587705033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585648005789478391803355 2378472008684217587705033)
              ·
                refine ⟨1783854006513163190778775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378472008684217587705033 1783854006513163190778775)
                ·
                  refine ⟨2675781009769744786168163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783854006513163190778775 2675781009769744786168163)
                  ·
                    refine ⟨4013671514654617179252245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2675781009769744786168163 4013671514654617179252245)
                    ·
                      refine ⟨188140852249435180277449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4013671514654617179252245 188140852249435180277449)
                      ·
                        rfl

theorem cell23_366403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_366403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366403 prefixEnd_366403 := by exact prefixLift 366403
  have htrace : WordTrace (prefixWord ++ tailWord_366403) baseStart_366403 baseEnd_366403 := by
    simpa [prefixWord, tailWord_366403, baseEnd_366403] using wordTrace_append hprefix tailTrace_366403
  have hstable : (prefixWord ++ tailWord_366403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366403).length < 2 ^ (prefixWord ++ tailWord_366403).sum := by decide
  have hdescent : baseEnd_366403 < baseStart_366403 := by decide
  rcases family_descends (prefixWord ++ tailWord_366403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366410 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_366410 : Nat := 118140960795 + 366410 * 2 ^ 59
def prefixEnd_366410 : Nat := 4983230072969 + 3 ^ 40 * 366410 * 2
def baseEnd_366410 : Nat := 188144446614016652889917

theorem tailTrace_366410 : CollatzResearch.WordTrace tailWord_366410 prefixEnd_366410 188144446614016652889917 := by
  unfold tailWord_366410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341017650641655672758171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8909380401711081794021789 3341017650641655672758171)
  ·
    refine ⟨5011526475962483509137257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3341017650641655672758171 5011526475962483509137257)
    ·
      refine ⟨3758644856971862631852943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5011526475962483509137257 3758644856971862631852943)
      ·
        refine ⟨5637967285457793947779415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3758644856971862631852943 5637967285457793947779415)
        ·
          refine ⟨8456950928186690921669123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5637967285457793947779415 8456950928186690921669123)
          ·
            refine ⟨12685426392280036382503685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8456950928186690921669123 12685426392280036382503685)
            ·
              refine ⟨2378517448552506821719441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12685426392280036382503685 2378517448552506821719441)
              ·
                refine ⟨1783888086414380116289581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378517448552506821719441 1783888086414380116289581)
                ·
                  refine ⟨668958032405392543608593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1783888086414380116289581 668958032405392543608593)
                  ·
                    refine ⟨501718524304044407706445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 668958032405392543608593 501718524304044407706445)
                    ·
                      refine ⟨188144446614016652889917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501718524304044407706445 188144446614016652889917)
                      ·
                        rfl

theorem cell23_366410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_366410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366410 prefixEnd_366410 := by exact prefixLift 366410
  have htrace : WordTrace (prefixWord ++ tailWord_366410) baseStart_366410 baseEnd_366410 := by
    simpa [prefixWord, tailWord_366410, baseEnd_366410] using wordTrace_append hprefix tailTrace_366410
  have hstable : (prefixWord ++ tailWord_366410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366410).length < 2 ^ (prefixWord ++ tailWord_366410).sum := by decide
  have hdescent : baseEnd_366410 < baseStart_366410 := by decide
  rcases family_descends (prefixWord ++ tailWord_366410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366417 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 2, 4]
def baseStart_366417 : Nat := 118140960795 + 366417 * 2 ^ 59
def prefixEnd_366417 : Nat := 4983230072969 + 3 ^ 40 * 366417 * 2
def baseEnd_366417 : Nat := 62716013659532708500795

theorem tailTrace_366417 : CollatzResearch.WordTrace tailWord_366417 prefixEnd_366417 62716013659532708500795 := by
  unfold tailWord_366417
  simp only [CollatzResearch.WordTrace]
  refine ⟨13364325913541262886537505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8909550609027508591025003 13364325913541262886537505)
  ·
    refine ⟨10023244435155947164903129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13364325913541262886537505 10023244435155947164903129)
    ·
      refine ⟨7517433326366960373677347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10023244435155947164903129 7517433326366960373677347)
      ·
        refine ⟨11276149989550440560516021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7517433326366960373677347 11276149989550440560516021)
        ·
          refine ⟨1057139061520353802548377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11276149989550440560516021 1057139061520353802548377)
          ·
            refine ⟨792854296140265351911283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1057139061520353802548377 792854296140265351911283)
            ·
              refine ⟨1189281444210398027866925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792854296140265351911283 1189281444210398027866925)
              ·
                refine ⟨445980541578899260450097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1189281444210398027866925 445980541578899260450097)
                ·
                  refine ⟨334485406184174445337573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445980541578899260450097 334485406184174445337573)
                  ·
                    refine ⟨62716013659532708500795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 334485406184174445337573 62716013659532708500795)
                    ·
                      rfl

theorem cell23_366417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_366417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366417 prefixEnd_366417 := by exact prefixLift 366417
  have htrace : WordTrace (prefixWord ++ tailWord_366417) baseStart_366417 baseEnd_366417 := by
    simpa [prefixWord, tailWord_366417, baseEnd_366417] using wordTrace_append hprefix tailTrace_366417
  have hstable : (prefixWord ++ tailWord_366417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366417).length < 2 ^ (prefixWord ++ tailWord_366417).sum := by decide
  have hdescent : baseEnd_366417 < baseStart_366417 := by decide
  rcases family_descends (prefixWord ++ tailWord_366417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366420 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_366420 : Nat := 118140960795 + 366420 * 2 ^ 59
def prefixEnd_366420 : Nat := 4983230072969 + 3 ^ 40 * 366420 * 2
def baseEnd_366420 : Nat := 188149581420561613764871

theorem tailTrace_366420 : CollatzResearch.WordTrace tailWord_366420 prefixEnd_366420 188149581420561613764871 := by
  unfold tailWord_366420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682217666265197199448357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8909623555020262932597809 6682217666265197199448357)
  ·
    refine ⟨1252915812424724474896567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6682217666265197199448357 1252915812424724474896567)
    ·
      refine ⟨1879373718637086712344851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252915812424724474896567 1879373718637086712344851)
      ·
        refine ⟨2819060577955630068517277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879373718637086712344851 2819060577955630068517277)
        ·
          refine ⟨1057147716733361275693979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2819060577955630068517277 1057147716733361275693979)
          ·
            refine ⟨1585721575100041913540969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057147716733361275693979 1585721575100041913540969)
            ·
              refine ⟨1189291181325031435155727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585721575100041913540969 1189291181325031435155727)
              ·
                refine ⟨1783936771987547152733591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189291181325031435155727 1783936771987547152733591)
                ·
                  refine ⟨2675905157981320729100387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1783936771987547152733591 2675905157981320729100387)
                  ·
                    refine ⟨4013857736971981093650581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2675905157981320729100387 4013857736971981093650581)
                    ·
                      refine ⟨188149581420561613764871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4013857736971981093650581 188149581420561613764871)
                      ·
                        rfl

theorem cell23_366420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_366420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366420 prefixEnd_366420 := by exact prefixLift 366420
  have htrace : WordTrace (prefixWord ++ tailWord_366420) baseStart_366420 baseEnd_366420 := by
    simpa [prefixWord, tailWord_366420, baseEnd_366420] using wordTrace_append hprefix tailTrace_366420
  have hstable : (prefixWord ++ tailWord_366420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366420).length < 2 ^ (prefixWord ++ tailWord_366420).sum := by decide
  have hdescent : baseEnd_366420 < baseStart_366420 := by decide
  rcases family_descends (prefixWord ++ tailWord_366420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366444 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 3]
def baseStart_366444 : Nat := 118140960795 + 366444 * 2 ^ 59
def prefixEnd_366444 : Nat := 4983230072969 + 3 ^ 40 * 366444 * 2
def baseEnd_366444 : Nat := 188161904956269519864761

theorem tailTrace_366444 : CollatzResearch.WordTrace tailWord_366444 prefixEnd_366444 188161904956269519864761 := by
  unfold tailWord_366444
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682655342221723248885193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8910207122962297665180257 6682655342221723248885193)
  ·
    refine ⟨5011991506666292436663895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6682655342221723248885193 5011991506666292436663895)
    ·
      refine ⟨7517987259999438654995843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011991506666292436663895 7517987259999438654995843)
      ·
        refine ⟨11276980889999157982493765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7517987259999438654995843 11276980889999157982493765)
        ·
          refine ⟨2114433916874842121717581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11276980889999157982493765 2114433916874842121717581)
          ·
            refine ⟨792912718828065795644093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2114433916874842121717581 792912718828065795644093)
            ·
              refine ⟨297342269560524673366535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 792912718828065795644093 297342269560524673366535)
              ·
                refine ⟨446013404340787010049803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297342269560524673366535 446013404340787010049803)
                ·
                  refine ⟨669020106511180515074705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446013404340787010049803 669020106511180515074705)
                  ·
                    refine ⟨501765079883385386306029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 669020106511180515074705 501765079883385386306029)
                    ·
                      refine ⟨188161904956269519864761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501765079883385386306029 188161904956269519864761)
                      ·
                        rfl

theorem cell23_366444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_366444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366444 prefixEnd_366444 := by exact prefixLift 366444
  have htrace : WordTrace (prefixWord ++ tailWord_366444) baseStart_366444 baseEnd_366444 := by
    simpa [prefixWord, tailWord_366444, baseEnd_366444] using wordTrace_append hprefix tailTrace_366444
  have hstable : (prefixWord ++ tailWord_366444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366444).length < 2 ^ (prefixWord ++ tailWord_366444).sum := by decide
  have hdescent : baseEnd_366444 < baseStart_366444 := by decide
  rcases family_descends (prefixWord ++ tailWord_366444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366467 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 3, 3, 2]
def baseStart_366467 : Nat := 118140960795 + 366467 * 2 ^ 59
def prefixEnd_366467 : Nat := 4983230072969 + 3 ^ 40 * 366467 * 2
def baseEnd_366467 : Nat := 188173715011322929877155

theorem tailTrace_366467 : CollatzResearch.WordTrace tailWord_366467 prefixEnd_366467 188173715011322929877155 := by
  unfold tailWord_366467
  simp only [CollatzResearch.WordTrace]
  refine ⟨13366149563360121425857655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8910766375573414283905103 13366149563360121425857655)
  ·
    refine ⟨20049224345040182138786483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13366149563360121425857655 20049224345040182138786483)
    ·
      refine ⟨30073836517560273208179725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20049224345040182138786483 30073836517560273208179725)
      ·
        refine ⟨11277688694085102453067397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30073836517560273208179725 11277688694085102453067397)
        ·
          refine ⟨2114566630140956709950137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11277688694085102453067397 2114566630140956709950137)
          ·
            refine ⟨1585924972605717532462603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2114566630140956709950137 1585924972605717532462603)
            ·
              refine ⟨2378887458908576298693905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585924972605717532462603 2378887458908576298693905)
              ·
                refine ⟨1784165594181432224020429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378887458908576298693905 1784165594181432224020429)
                ·
                  refine ⟨669062097818037084007661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1784165594181432224020429 669062097818037084007661)
                  ·
                    refine ⟨250898286681763906502873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669062097818037084007661 250898286681763906502873)
                    ·
                      refine ⟨188173715011322929877155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250898286681763906502873 188173715011322929877155)
                      ·
                        rfl

theorem cell23_366467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_366467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366467 prefixEnd_366467 := by exact prefixLift 366467
  have htrace : WordTrace (prefixWord ++ tailWord_366467) baseStart_366467 baseEnd_366467 := by
    simpa [prefixWord, tailWord_366467, baseEnd_366467] using wordTrace_append hprefix tailTrace_366467
  have hstable : (prefixWord ++ tailWord_366467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366467).length < 2 ^ (prefixWord ++ tailWord_366467).sum := by decide
  have hdescent : baseEnd_366467 < baseStart_366467 := by decide
  rcases family_descends (prefixWord ++ tailWord_366467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366474 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_366474 : Nat := 118140960795 + 366474 * 2 ^ 59
def prefixEnd_366474 : Nat := 4983230072969 + 3 ^ 40 * 366474 * 2
def baseEnd_366474 : Nat := 188177309375904402489623

theorem tailTrace_366474 : CollatzResearch.WordTrace tailWord_366474 prefixEnd_366474 188177309375904402489623 := by
  unfold tailWord_366474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341601218583690405340619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8910936582889841080908317 3341601218583690405340619)
  ·
    refine ⟨5012401827875535608010929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3341601218583690405340619 5012401827875535608010929)
    ·
      refine ⟨3759301370906651706008197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5012401827875535608010929 3759301370906651706008197)
      ·
        refine ⟨704869007044997194876537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3759301370906651706008197 704869007044997194876537)
        ·
          refine ⟨528651755283747896157403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704869007044997194876537 528651755283747896157403)
          ·
            refine ⟨792977632925621844236105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528651755283747896157403 792977632925621844236105)
            ·
              refine ⟨594733224694216383177079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792977632925621844236105 594733224694216383177079)
              ·
                refine ⟨892099837041324574765619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594733224694216383177079 892099837041324574765619)
                ·
                  refine ⟨1338149755561986862148429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892099837041324574765619 1338149755561986862148429)
                  ·
                    refine ⟨501806158335745073305661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1338149755561986862148429 501806158335745073305661)
                    ·
                      refine ⟨188177309375904402489623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 501806158335745073305661 188177309375904402489623)
                      ·
                        rfl

theorem cell23_366474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_366474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366474 prefixEnd_366474 := by exact prefixLift 366474
  have htrace : WordTrace (prefixWord ++ tailWord_366474) baseStart_366474 baseEnd_366474 := by
    simpa [prefixWord, tailWord_366474, baseEnd_366474] using wordTrace_append hprefix tailTrace_366474
  have hstable : (prefixWord ++ tailWord_366474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366474).length < 2 ^ (prefixWord ++ tailWord_366474).sum := by decide
  have hdescent : baseEnd_366474 < baseStart_366474 := by decide
  rcases family_descends (prefixWord ++ tailWord_366474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366484 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_366484 : Nat := 118140960795 + 366484 * 2 ^ 59
def prefixEnd_366484 : Nat := 4983230072969 + 3 ^ 40 * 366484 * 2
def baseEnd_366484 : Nat := 188182444182449363364577

theorem tailTrace_366484 : CollatzResearch.WordTrace tailWord_366484 prefixEnd_366484 188182444182449363364577 := by
  unfold tailWord_366484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683384802149266664613253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8911179736199022219484337 6683384802149266664613253)
  ·
    refine ⟨1253134650402987499614985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6683384802149266664613253 1253134650402987499614985)
    ·
      refine ⟨939850987802240624711239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1253134650402987499614985 939850987802240624711239)
      ·
        refine ⟨1409776481703360937066859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939850987802240624711239 1409776481703360937066859)
        ·
          refine ⟨2114664722555041405600289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1409776481703360937066859 2114664722555041405600289)
          ·
            refine ⟨1585998541916281054200217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2114664722555041405600289 1585998541916281054200217)
            ·
              refine ⟨1189498906437210790650163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1585998541916281054200217 1189498906437210790650163)
              ·
                refine ⟨1784248359655816185975245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189498906437210790650163 1784248359655816185975245)
                ·
                  refine ⟨669093134870931069740717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1784248359655816185975245 669093134870931069740717)
                  ·
                    refine ⟨250909925576599151152769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669093134870931069740717 250909925576599151152769)
                    ·
                      refine ⟨188182444182449363364577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250909925576599151152769 188182444182449363364577)
                      ·
                        rfl

theorem cell23_366484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_366484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366484 prefixEnd_366484 := by exact prefixLift 366484
  have htrace : WordTrace (prefixWord ++ tailWord_366484) baseStart_366484 baseEnd_366484 := by
    simpa [prefixWord, tailWord_366484, baseEnd_366484] using wordTrace_append hprefix tailTrace_366484
  have hstable : (prefixWord ++ tailWord_366484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366484).length < 2 ^ (prefixWord ++ tailWord_366484).sum := by decide
  have hdescent : baseEnd_366484 < baseStart_366484 := by decide
  rcases family_descends (prefixWord ++ tailWord_366484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366520 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 7]
def baseStart_366520 : Nat := 118140960795 + 366520 * 2 ^ 59
def prefixEnd_366520 : Nat := 4983230072969 + 3 ^ 40 * 366520 * 2
def baseEnd_366520 : Nat := 20911214387334580279379

theorem tailTrace_366520 : CollatzResearch.WordTrace tailWord_366520 prefixEnd_366520 20911214387334580279379 := by
  unfold tailWord_366520
  simp only [CollatzResearch.WordTrace]
  refine ⟨6684041316084055738768507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8912055088112074318358009 6684041316084055738768507)
  ·
    refine ⟨10026061974126083608152761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6684041316084055738768507 10026061974126083608152761)
    ·
      refine ⟨7519546480594562706114571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10026061974126083608152761 7519546480594562706114571)
      ·
        refine ⟨11279319720891844059171857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7519546480594562706114571 11279319720891844059171857)
        ·
          refine ⟨8459489790668883044378893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11279319720891844059171857 8459489790668883044378893)
          ·
            refine ⟨3172308671500831141642085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8459489790668883044378893 3172308671500831141642085)
            ·
              refine ⟨594807875906405839057891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3172308671500831141642085 594807875906405839057891)
              ·
                refine ⟨892211813859608758586837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 594807875906405839057891 892211813859608758586837)
                ·
                  refine ⟨20911214387334580279379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 892211813859608758586837 20911214387334580279379)
                  ·
                    rfl

theorem cell23_366520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 7].length) (baseStart_366520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366520 prefixEnd_366520 := by exact prefixLift 366520
  have htrace : WordTrace (prefixWord ++ tailWord_366520) baseStart_366520 baseEnd_366520 := by
    simpa [prefixWord, tailWord_366520, baseEnd_366520] using wordTrace_append hprefix tailTrace_366520
  have hstable : (prefixWord ++ tailWord_366520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366520).length < 2 ^ (prefixWord ++ tailWord_366520).sum := by decide
  have hdescent : baseEnd_366520 < baseStart_366520 := by decide
  rcases family_descends (prefixWord ++ tailWord_366520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366523 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8]
def baseStart_366523 : Nat := 118140960795 + 366523 * 2 ^ 59
def prefixEnd_366523 : Nat := 4983230072969 + 3 ^ 40 * 366523 * 2
def baseEnd_366523 : Nat := 188202469927974710776897

theorem tailTrace_366523 : CollatzResearch.WordTrace tailWord_366523 prefixEnd_366523 188202469927974710776897 := by
  unfold tailWord_366523
  simp only [CollatzResearch.WordTrace]
  refine ⟨13368192051157242989896223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8912128034104828659930815 13368192051157242989896223)
  ·
    refine ⟨20052288076735864484844335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13368192051157242989896223 20052288076735864484844335)
    ·
      refine ⟨30078432115103796727266503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20052288076735864484844335 30078432115103796727266503)
      ·
        refine ⟨45117648172655695090899755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30078432115103796727266503 45117648172655695090899755)
        ·
          refine ⟨67676472258983542636349633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45117648172655695090899755 67676472258983542636349633)
          ·
            refine ⟨50757354194237656977262225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67676472258983542636349633 50757354194237656977262225)
            ·
              refine ⟨38068015645678242732946669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50757354194237656977262225 38068015645678242732946669)
              ·
                refine ⟨14275505867129341024855001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38068015645678242732946669 14275505867129341024855001)
                ·
                  refine ⟨10706629400347005768641251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14275505867129341024855001 10706629400347005768641251)
                  ·
                    refine ⟨16059944100520508652961877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10706629400347005768641251 16059944100520508652961877)
                    ·
                      refine ⟨188202469927974710776897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 16059944100520508652961877 188202469927974710776897)
                      ·
                        rfl

theorem cell23_366523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_366523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366523 prefixEnd_366523 := by exact prefixLift 366523
  have htrace : WordTrace (prefixWord ++ tailWord_366523) baseStart_366523 baseEnd_366523 := by
    simpa [prefixWord, tailWord_366523, baseEnd_366523] using wordTrace_append hprefix tailTrace_366523
  have hstable : (prefixWord ++ tailWord_366523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366523).length < 2 ^ (prefixWord ++ tailWord_366523).sum := by decide
  have hdescent : baseEnd_366523 < baseStart_366523 := by decide
  rcases family_descends (prefixWord ++ tailWord_366523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366577 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 5]
def baseStart_366577 : Nat := 118140960795 + 366577 * 2 ^ 59
def prefixEnd_366577 : Nat := 4983230072969 + 3 ^ 40 * 366577 * 2
def baseEnd_366577 : Nat := 188230197883317499501649

theorem tailTrace_366577 : CollatzResearch.WordTrace tailWord_366577 prefixEnd_366577 188230197883317499501649 := by
  unfold tailWord_366577
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370161592961610212361985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8913441061974406808241323 13370161592961610212361985)
  ·
    refine ⟨10027621194721207659271489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13370161592961610212361985 10027621194721207659271489)
    ·
      refine ⟨7520715896040905744453617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10027621194721207659271489 7520715896040905744453617)
      ·
        refine ⟨5640536922030679308340213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7520715896040905744453617 5640536922030679308340213)
        ·
          refine ⟨528800336440376185156895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5640536922030679308340213 528800336440376185156895)
          ·
            refine ⟨793200504660564277735343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528800336440376185156895 793200504660564277735343)
            ·
              refine ⟨1189800756990846416603015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793200504660564277735343 1189800756990846416603015)
              ·
                refine ⟨1784701135486269624904523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1189800756990846416603015 1784701135486269624904523)
                ·
                  refine ⟨2677051703229404437356785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1784701135486269624904523 2677051703229404437356785)
                  ·
                    refine ⟨2007788777422053328017589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2677051703229404437356785 2007788777422053328017589)
                    ·
                      refine ⟨188230197883317499501649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2007788777422053328017589 188230197883317499501649)
                      ·
                        rfl

theorem cell23_366577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_366577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366577 prefixEnd_366577 := by exact prefixLift 366577
  have htrace : WordTrace (prefixWord ++ tailWord_366577) baseStart_366577 baseEnd_366577 := by
    simpa [prefixWord, tailWord_366577, baseEnd_366577] using wordTrace_append hprefix tailTrace_366577
  have hstable : (prefixWord ++ tailWord_366577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366577).length < 2 ^ (prefixWord ++ tailWord_366577).sum := by decide
  have hdescent : baseEnd_366577 < baseStart_366577 := by decide
  rcases family_descends (prefixWord ++ tailWord_366577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366582 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_366582 : Nat := 118140960795 + 366582 * 2 ^ 59
def prefixEnd_366582 : Nat := 4983230072969 + 3 ^ 40 * 366582 * 2
def baseEnd_366582 : Nat := 188232765286589979939127

theorem tailTrace_366582 : CollatzResearch.WordTrace tailWord_366582 prefixEnd_366582 188232765286589979939127 := by
  unfold tailWord_366582
  simp only [CollatzResearch.WordTrace]
  refine ⟨835646497371468504143375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8913562638628997377529333 835646497371468504143375)
  ·
    refine ⟨1253469746057202756215063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 835646497371468504143375 1253469746057202756215063)
    ·
      refine ⟨1880204619085804134322595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253469746057202756215063 1880204619085804134322595)
      ·
        refine ⟨2820306928628706201483893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880204619085804134322595 2820306928628706201483893)
        ·
          refine ⟨264403774558941206389115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2820306928628706201483893 264403774558941206389115)
          ·
            refine ⟨396605661838411809583673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264403774558941206389115 396605661838411809583673)
            ·
              refine ⟨297454246378808857187755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396605661838411809583673 297454246378808857187755)
              ·
                refine ⟨446181369568213285781633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297454246378808857187755 446181369568213285781633)
                ·
                  refine ⟨334636027176159964336225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446181369568213285781633 334636027176159964336225)
                  ·
                    refine ⟨250977020382119973252169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334636027176159964336225 250977020382119973252169)
                    ·
                      refine ⟨188232765286589979939127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250977020382119973252169 188232765286589979939127)
                      ·
                        rfl

theorem cell23_366582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_366582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366582 prefixEnd_366582 := by exact prefixLift 366582
  have htrace : WordTrace (prefixWord ++ tailWord_366582) baseStart_366582 baseEnd_366582 := by
    simpa [prefixWord, tailWord_366582, baseEnd_366582] using wordTrace_append hprefix tailTrace_366582
  have hstable : (prefixWord ++ tailWord_366582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366582).length < 2 ^ (prefixWord ++ tailWord_366582).sum := by decide
  have hdescent : baseEnd_366582 < baseStart_366582 := by decide
  rcases family_descends (prefixWord ++ tailWord_366582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366587 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 2, 4, 2]
def baseStart_366587 : Nat := 118140960795 + 366587 * 2 ^ 59
def prefixEnd_366587 : Nat := 4983230072969 + 3 ^ 40 * 366587 * 2
def baseEnd_366587 : Nat := 188235332689862460376603

theorem tailTrace_366587 : CollatzResearch.WordTrace tailWord_366587 prefixEnd_366587 188235332689862460376603 := by
  unfold tailWord_366587
  simp only [CollatzResearch.WordTrace]
  refine ⟨13370526322925381920226015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8913684215283587946817343 13370526322925381920226015)
  ·
    refine ⟨20055789484388072880339023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13370526322925381920226015 20055789484388072880339023)
    ·
      refine ⟨30083684226582109320508535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20055789484388072880339023 30083684226582109320508535)
      ·
        refine ⟨45125526339873163980762803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30083684226582109320508535 45125526339873163980762803)
        ·
          refine ⟨67688289509809745971144205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45125526339873163980762803 67688289509809745971144205)
          ·
            refine ⟨25383108566178654739179077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67688289509809745971144205 25383108566178654739179077)
            ·
              refine ⟨4759332856158497763596077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25383108566178654739179077 4759332856158497763596077)
              ·
                refine ⟨1784749821059436661348529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4759332856158497763596077 1784749821059436661348529)
                ·
                  refine ⟨1338562365794577496011397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1784749821059436661348529 1338562365794577496011397)
                  ·
                    refine ⟨250980443586483280502137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1338562365794577496011397 250980443586483280502137)
                    ·
                      refine ⟨188235332689862460376603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 250980443586483280502137 188235332689862460376603)
                      ·
                        rfl

theorem cell23_366587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4, 2].length) (baseStart_366587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366587 prefixEnd_366587 := by exact prefixLift 366587
  have htrace : WordTrace (prefixWord ++ tailWord_366587) baseStart_366587 baseEnd_366587 := by
    simpa [prefixWord, tailWord_366587, baseEnd_366587] using wordTrace_append hprefix tailTrace_366587
  have hstable : (prefixWord ++ tailWord_366587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366587).length < 2 ^ (prefixWord ++ tailWord_366587).sum := by decide
  have hdescent : baseEnd_366587 < baseStart_366587 := by decide
  rcases family_descends (prefixWord ++ tailWord_366587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366627 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 6]
def baseStart_366627 : Nat := 118140960795 + 366627 * 2 ^ 59
def prefixEnd_366627 : Nat := 4983230072969 + 3 ^ 40 * 366627 * 2
def baseEnd_366627 : Nat := 20917319101782478208491

theorem tailTrace_366627 : CollatzResearch.WordTrace tailWord_366627 prefixEnd_366627 20917319101782478208491 := by
  unfold tailWord_366627
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371985242780468751682135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8914656828520312501121423 13371985242780468751682135)
  ·
    refine ⟨20057977864170703127523203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13371985242780468751682135 20057977864170703127523203)
    ·
      refine ⟨30086966796256054691284805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20057977864170703127523203 30086966796256054691284805)
      ·
        refine ⟨5641306274298010254615901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30086966796256054691284805 5641306274298010254615901)
        ·
          refine ⟨2115489852861753845480963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5641306274298010254615901 2115489852861753845480963)
          ·
            refine ⟨3173234779292630768221445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115489852861753845480963 3173234779292630768221445)
            ·
              refine ⟨594981521117368269041521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3173234779292630768221445 594981521117368269041521)
              ·
                refine ⟨446236140838026201781141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 594981521117368269041521 446236140838026201781141)
                ·
                  refine ⟨20917319101782478208491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 446236140838026201781141 20917319101782478208491)
                  ·
                    rfl

theorem cell23_366627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 6].length) (baseStart_366627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366627 prefixEnd_366627 := by exact prefixLift 366627
  have htrace : WordTrace (prefixWord ++ tailWord_366627) baseStart_366627 baseEnd_366627 := by
    simpa [prefixWord, tailWord_366627, baseEnd_366627] using wordTrace_append hprefix tailTrace_366627
  have hstable : (prefixWord ++ tailWord_366627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366627).length < 2 ^ (prefixWord ++ tailWord_366627).sum := by decide
  have hdescent : baseEnd_366627 < baseStart_366627 := by decide
  rcases family_descends (prefixWord ++ tailWord_366627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366650 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_366650 : Nat := 118140960795 + 366650 * 2 ^ 59
def prefixEnd_366650 : Nat := 4983230072969 + 3 ^ 40 * 366650 * 2
def baseEnd_366650 : Nat := 188267681971095713888813

theorem tailTrace_366650 : CollatzResearch.WordTrace tailWord_366650 prefixEnd_366650 188267681971095713888813 := by
  unfold tailWord_366650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3343206030424285919942351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8915216081131429119846269 3343206030424285919942351)
  ·
    refine ⟨5014809045636428879913527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3343206030424285919942351 5014809045636428879913527)
    ·
      refine ⟨7522213568454643319870291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5014809045636428879913527 7522213568454643319870291)
      ·
        refine ⟨11283320352681964979805437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7522213568454643319870291 11283320352681964979805437)
        ·
          refine ⟨4231245132255736867427039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11283320352681964979805437 4231245132255736867427039)
          ·
            refine ⟨6346867698383605301140559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231245132255736867427039 6346867698383605301140559)
            ·
              refine ⟨9520301547575407951710839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6346867698383605301140559 9520301547575407951710839)
              ·
                refine ⟨14280452321363111927566259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9520301547575407951710839 14280452321363111927566259)
                ·
                  refine ⟨21420678482044667891349389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14280452321363111927566259 21420678482044667891349389)
                  ·
                    refine ⟨8032754430766750459256021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21420678482044667891349389 8032754430766750459256021)
                    ·
                      refine ⟨188267681971095713888813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8032754430766750459256021 188267681971095713888813)
                      ·
                        rfl

theorem cell23_366650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_366650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366650 prefixEnd_366650 := by exact prefixLift 366650
  have htrace : WordTrace (prefixWord ++ tailWord_366650) baseStart_366650 baseEnd_366650 := by
    simpa [prefixWord, tailWord_366650, baseEnd_366650] using wordTrace_append hprefix tailTrace_366650
  have hstable : (prefixWord ++ tailWord_366650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366650).length < 2 ^ (prefixWord ++ tailWord_366650).sum := by decide
  have hdescent : baseEnd_366650 < baseStart_366650 := by decide
  rcases family_descends (prefixWord ++ tailWord_366650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366664 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_366664 : Nat := 118140960795 + 366664 * 2 ^ 59
def prefixEnd_366664 : Nat := 4983230072969 + 3 ^ 40 * 366664 * 2
def baseEnd_366664 : Nat := 188274870700258659113749

theorem tailTrace_366664 : CollatzResearch.WordTrace tailWord_366664 prefixEnd_366664 188274870700258659113749 := by
  unfold tailWord_366664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686667371823212035389523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8915556495764282713852697 6686667371823212035389523)
  ·
    refine ⟨10030001057734818053084285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6686667371823212035389523 10030001057734818053084285)
    ·
      refine ⟨3761250396650556769906607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10030001057734818053084285 3761250396650556769906607)
      ·
        refine ⟨5641875594975835154859911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761250396650556769906607 5641875594975835154859911)
        ·
          refine ⟨8462813392463752732289867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5641875594975835154859911 8462813392463752732289867)
          ·
            refine ⟨12694220088695629098434801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462813392463752732289867 12694220088695629098434801)
            ·
              refine ⟨9520665066521721823826101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12694220088695629098434801 9520665066521721823826101)
              ·
                refine ⟨892562349986411420983697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9520665066521721823826101 892562349986411420983697)
                ·
                  refine ⟨669421762489808565737773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892562349986411420983697 669421762489808565737773)
                  ·
                    refine ⟨251033160933678212151665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669421762489808565737773 251033160933678212151665)
                    ·
                      refine ⟨188274870700258659113749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251033160933678212151665 188274870700258659113749)
                      ·
                        rfl

theorem cell23_366664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_366664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366664 prefixEnd_366664 := by exact prefixLift 366664
  have htrace : WordTrace (prefixWord ++ tailWord_366664) baseStart_366664 baseEnd_366664 := by
    simpa [prefixWord, tailWord_366664, baseEnd_366664] using wordTrace_append hprefix tailTrace_366664
  have hstable : (prefixWord ++ tailWord_366664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366664).length < 2 ^ (prefixWord ++ tailWord_366664).sum := by decide
  have hdescent : baseEnd_366664 < baseStart_366664 := by decide
  rcases family_descends (prefixWord ++ tailWord_366664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366678 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_366678 : Nat := 118140960795 + 366678 * 2 ^ 59
def prefixEnd_366678 : Nat := 4983230072969 + 3 ^ 40 * 366678 * 2
def baseEnd_366678 : Nat := 20920228825491289370965

theorem tailTrace_366678 : CollatzResearch.WordTrace tailWord_366678 prefixEnd_366678 20920228825491289370965 := by
  unfold tailWord_366678
  simp only [CollatzResearch.WordTrace]
  refine ⟨835865335349731528861793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8915896910397136307859125 835865335349731528861793)
  ·
    refine ⟨626899001512298646646345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 835865335349731528861793 626899001512298646646345)
    ·
      refine ⟨470174251134223984984759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626899001512298646646345 470174251134223984984759)
      ·
        refine ⟨705261376701335977477139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470174251134223984984759 705261376701335977477139)
        ·
          refine ⟨1057892065052003966215709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705261376701335977477139 1057892065052003966215709)
          ·
            refine ⟨396709524394501487330891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1057892065052003966215709 396709524394501487330891)
            ·
              refine ⟨595064286591752230996337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396709524394501487330891 595064286591752230996337)
              ·
                refine ⟨446298214943814173247253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595064286591752230996337 446298214943814173247253)
                ·
                  refine ⟨20920228825491289370965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 446298214943814173247253 20920228825491289370965)
                  ·
                    rfl

theorem cell23_366678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_366678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366678 prefixEnd_366678 := by exact prefixLift 366678
  have htrace : WordTrace (prefixWord ++ tailWord_366678) baseStart_366678 baseEnd_366678 := by
    simpa [prefixWord, tailWord_366678, baseEnd_366678] using wordTrace_append hprefix tailTrace_366678
  have hstable : (prefixWord ++ tailWord_366678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366678).length < 2 ^ (prefixWord ++ tailWord_366678).sum := by decide
  have hdescent : baseEnd_366678 < baseStart_366678 := by decide
  rcases family_descends (prefixWord ++ tailWord_366678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366697 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_366697 : Nat := 118140960795 + 366697 * 2 ^ 59
def prefixEnd_366697 : Nat := 4983230072969 + 3 ^ 40 * 366697 * 2
def baseEnd_366697 : Nat := 188291815561857030001097

theorem tailTrace_366697 : CollatzResearch.WordTrace tailWord_366697 prefixEnd_366697 188291815561857030001097 := by
  unfold tailWord_366697
  simp only [CollatzResearch.WordTrace]
  refine ⟨13374538352526870706730345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8916358901684580471153563 13374538352526870706730345)
  ·
    refine ⟨10030903764395153030047759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13374538352526870706730345 10030903764395153030047759)
    ·
      refine ⟨15046355646592729545071639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10030903764395153030047759 15046355646592729545071639)
      ·
        refine ⟨22569533469889094317607459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15046355646592729545071639 22569533469889094317607459)
        ·
          refine ⟨33854300204833641476411189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22569533469889094317607459 33854300204833641476411189)
          ·
            refine ⟨3173840644203153888413549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33854300204833641476411189 3173840644203153888413549)
            ·
              refine ⟨1190190241576182708155081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3173840644203153888413549 1190190241576182708155081)
              ·
                refine ⟨892642681182137031116311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190190241576182708155081 892642681182137031116311)
                ·
                  refine ⟨1338964021773205546674467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892642681182137031116311 1338964021773205546674467)
                  ·
                    refine ⟨2008446032659808320011701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1338964021773205546674467 2008446032659808320011701)
                    ·
                      refine ⟨188291815561857030001097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2008446032659808320011701 188291815561857030001097)
                      ·
                        rfl

theorem cell23_366697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_366697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366697 prefixEnd_366697 := by exact prefixLift 366697
  have htrace : WordTrace (prefixWord ++ tailWord_366697) baseStart_366697 baseEnd_366697 := by
    simpa [prefixWord, tailWord_366697, baseEnd_366697] using wordTrace_append hprefix tailTrace_366697
  have hstable : (prefixWord ++ tailWord_366697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366697).length < 2 ^ (prefixWord ++ tailWord_366697).sum := by decide
  have hdescent : baseEnd_366697 < baseStart_366697 := by decide
  rcases family_descends (prefixWord ++ tailWord_366697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366704 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 1, 6]
def baseStart_366704 : Nat := 118140960795 + 366704 * 2 ^ 59
def prefixEnd_366704 : Nat := 4983230072969 + 3 ^ 40 * 366704 * 2
def baseEnd_366704 : Nat := 62765136642146167537855

theorem tailTrace_366704 : CollatzResearch.WordTrace tailWord_366704 prefixEnd_366704 62765136642146167537855 := by
  unfold tailWord_366704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687396831750755451117583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8916529109001007268156777 6687396831750755451117583)
  ·
    refine ⟨10031095247626133176676375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6687396831750755451117583 10031095247626133176676375)
    ·
      refine ⟨15046642871439199765014563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10031095247626133176676375 15046642871439199765014563)
      ·
        refine ⟨22569964307158799647521845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15046642871439199765014563 22569964307158799647521845)
        ·
          refine ⟨2115934153796137466955173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22569964307158799647521845 2115934153796137466955173)
          ·
            refine ⟨396737653836775775054095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2115934153796137466955173 396737653836775775054095)
            ·
              refine ⟨595106480755163662581143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396737653836775775054095 595106480755163662581143)
              ·
                refine ⟨892659721132745493871715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595106480755163662581143 892659721132745493871715)
                ·
                  refine ⟨1338989581699118240807573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892659721132745493871715 1338989581699118240807573)
                  ·
                    refine ⟨62765136642146167537855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1338989581699118240807573 62765136642146167537855)
                    ·
                      rfl

theorem cell23_366704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_366704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366704 prefixEnd_366704 := by exact prefixLift 366704
  have htrace : WordTrace (prefixWord ++ tailWord_366704) baseStart_366704 baseEnd_366704 := by
    simpa [prefixWord, tailWord_366704, baseEnd_366704] using wordTrace_append hprefix tailTrace_366704
  have hstable : (prefixWord ++ tailWord_366704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366704).length < 2 ^ (prefixWord ++ tailWord_366704).sum := by decide
  have hdescent : baseEnd_366704 < baseStart_366704 := by decide
  rcases family_descends (prefixWord ++ tailWord_366704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366711 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 3, 2, 2]
def baseStart_366711 : Nat := 118140960795 + 366711 * 2 ^ 59
def prefixEnd_366711 : Nat := 4983230072969 + 3 ^ 40 * 366711 * 2
def baseEnd_366711 : Nat := 188299004291019975226033

theorem tailTrace_366711 : CollatzResearch.WordTrace tailWord_366711 prefixEnd_366711 188299004291019975226033 := by
  unfold tailWord_366711
  simp only [CollatzResearch.WordTrace]
  refine ⟨13375048974476151097739987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8916699316317434065159991 13375048974476151097739987)
  ·
    refine ⟨20062573461714226646609981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13375048974476151097739987 20062573461714226646609981)
    ·
      refine ⟨7523465048142834992478743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20062573461714226646609981 7523465048142834992478743)
      ·
        refine ⟨11285197572214252488718115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7523465048142834992478743 11285197572214252488718115)
        ·
          refine ⟨16927796358321378733077173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11285197572214252488718115 16927796358321378733077173)
          ·
            refine ⟨1586980908592629256225985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16927796358321378733077173 1586980908592629256225985)
            ·
              refine ⟨1190235681444471942169489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586980908592629256225985 1190235681444471942169489)
              ·
                refine ⟨892676761083353956627117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190235681444471942169489 892676761083353956627117)
                ·
                  refine ⟨334753785406257733735169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 892676761083353956627117 334753785406257733735169)
                  ·
                    refine ⟨251065339054693300301377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334753785406257733735169 251065339054693300301377)
                    ·
                      refine ⟨188299004291019975226033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251065339054693300301377 188299004291019975226033)
                      ·
                        rfl

theorem cell23_366711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_366711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366711 prefixEnd_366711 := by exact prefixLift 366711
  have htrace : WordTrace (prefixWord ++ tailWord_366711) baseStart_366711 baseEnd_366711 := by
    simpa [prefixWord, tailWord_366711, baseEnd_366711] using wordTrace_append hprefix tailTrace_366711
  have hstable : (prefixWord ++ tailWord_366711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366711).length < 2 ^ (prefixWord ++ tailWord_366711).sum := by decide
  have hdescent : baseEnd_366711 < baseStart_366711 := by decide
  rcases family_descends (prefixWord ++ tailWord_366711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366717 : List Nat := [1, 4, 1, 1, 3, 3, 1, 9]
def baseStart_366717 : Nat := 118140960795 + 366717 * 2 ^ 59
def prefixEnd_366717 : Nat := 4983230072969 + 3 ^ 40 * 366717 * 2
def baseEnd_366717 : Nat := 6974151302775813027815

theorem tailTrace_366717 : CollatzResearch.WordTrace tailWord_366717 prefixEnd_366717 6974151302775813027815 := by
  unfold tailWord_366717
  simp only [CollatzResearch.WordTrace]
  refine ⟨13375267812454414122458405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8916845208302942748305603 13375267812454414122458405)
  ·
    refine ⟨2507862714835202647960951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13375267812454414122458405 2507862714835202647960951)
    ·
      refine ⟨3761794072252803971941427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507862714835202647960951 3761794072252803971941427)
      ·
        refine ⟨5642691108379205957912141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3761794072252803971941427 5642691108379205957912141)
        ·
          refine ⟨2116009165642202234217053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5642691108379205957912141 2116009165642202234217053)
          ·
            refine ⟨793503437115825837831395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2116009165642202234217053 793503437115825837831395)
            ·
              refine ⟨1190255155673738756747093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793503437115825837831395 1190255155673738756747093)
              ·
                refine ⟨6974151302775813027815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1190255155673738756747093 6974151302775813027815)
                ·
                  rfl

theorem cell23_366717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 9].length) (baseStart_366717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366717 prefixEnd_366717 := by exact prefixLift 366717
  have htrace : WordTrace (prefixWord ++ tailWord_366717) baseStart_366717 baseEnd_366717 := by
    simpa [prefixWord, tailWord_366717, baseEnd_366717] using wordTrace_append hprefix tailTrace_366717
  have hstable : (prefixWord ++ tailWord_366717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366717).length < 2 ^ (prefixWord ++ tailWord_366717).sum := by decide
  have hdescent : baseEnd_366717 < baseStart_366717 := by decide
  rcases family_descends (prefixWord ++ tailWord_366717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366734 : List Nat := [4, 1, 1, 3, 3, 2, 9]
def baseStart_366734 : Nat := 118140960795 + 366734 * 2 ^ 59
def prefixEnd_366734 : Nat := 4983230072969 + 3 ^ 40 * 366734 * 2
def baseEnd_366734 : Nat := 2324824868470041793067

theorem tailTrace_366734 : CollatzResearch.WordTrace tailWord_366734 prefixEnd_366734 2324824868470041793067 := by
  unfold tailWord_366734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671985981674103253228407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8917258568928550683884837 1671985981674103253228407)
  ·
    refine ⟨2507978972511154879842611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1671985981674103253228407 2507978972511154879842611)
    ·
      refine ⟨3761968458766732319763917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2507978972511154879842611 3761968458766732319763917)
      ·
        refine ⟨1410738172037524619911469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3761968458766732319763917 1410738172037524619911469)
        ·
          refine ⟨529026814514071732466801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1410738172037524619911469 529026814514071732466801)
          ·
            refine ⟨396770110885553799350101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529026814514071732466801 396770110885553799350101)
            ·
              refine ⟨2324824868470041793067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 396770110885553799350101 2324824868470041793067)
              ·
                rfl

theorem cell23_366734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 9].length) (baseStart_366734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366734 prefixEnd_366734 := by exact prefixLift 366734
  have htrace : WordTrace (prefixWord ++ tailWord_366734) baseStart_366734 baseEnd_366734 := by
    simpa [prefixWord, tailWord_366734, baseEnd_366734] using wordTrace_append hprefix tailTrace_366734
  have hstable : (prefixWord ++ tailWord_366734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366734).length < 2 ^ (prefixWord ++ tailWord_366734).sum := by decide
  have hdescent : baseEnd_366734 < baseStart_366734 := by decide
  rcases family_descends (prefixWord ++ tailWord_366734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366796 : List Nat := [2, 2, 1, 6, 2, 1, 2, 2, 1, 2, 2]
def baseStart_366796 : Nat := 118140960795 + 366796 * 2 ^ 59
def prefixEnd_366796 : Nat := 4983230072969 + 3 ^ 40 * 366796 * 2
def baseEnd_366796 : Nat := 188342650146652142663143

theorem tailTrace_366796 : CollatzResearch.WordTrace tailWord_366796 prefixEnd_366796 188342650146652142663143 := by
  unfold tailWord_366796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689074589584105307292121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8918766119445473743056161 6689074589584105307292121)
  ·
    refine ⟨5016805942188078980469091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6689074589584105307292121 5016805942188078980469091)
    ·
      refine ⟨7525208913282118470703637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5016805942188078980469091 7525208913282118470703637)
      ·
        refine ⟨352744167810099303314233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7525208913282118470703637 352744167810099303314233)
        ·
          refine ⟨264558125857574477485675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352744167810099303314233 264558125857574477485675)
          ·
            refine ⟨396837188786361716228513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264558125857574477485675 396837188786361716228513)
            ·
              refine ⟨297627891589771287171385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396837188786361716228513 297627891589771287171385)
              ·
                refine ⟨223220918692328465378539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297627891589771287171385 223220918692328465378539)
                ·
                  refine ⟨334831378038492698067809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223220918692328465378539 334831378038492698067809)
                  ·
                    refine ⟨251123533528869523550857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334831378038492698067809 251123533528869523550857)
                    ·
                      refine ⟨188342650146652142663143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251123533528869523550857 188342650146652142663143)
                      ·
                        rfl

theorem cell23_366796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_366796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366796 prefixEnd_366796 := by exact prefixLift 366796
  have htrace : WordTrace (prefixWord ++ tailWord_366796) baseStart_366796 baseEnd_366796 := by
    simpa [prefixWord, tailWord_366796, baseEnd_366796] using wordTrace_append hprefix tailTrace_366796
  have hstable : (prefixWord ++ tailWord_366796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366796).length < 2 ^ (prefixWord ++ tailWord_366796).sum := by decide
  have hdescent : baseEnd_366796 < baseStart_366796 := by decide
  rcases family_descends (prefixWord ++ tailWord_366796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366801 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 4, 2, 2]
def baseStart_366801 : Nat := 118140960795 + 366801 * 2 ^ 59
def prefixEnd_366801 : Nat := 4983230072969 + 3 ^ 40 * 366801 * 2
def baseEnd_366801 : Nat := 188345217549924623100619

theorem tailTrace_366801 : CollatzResearch.WordTrace tailWord_366801 prefixEnd_366801 188345217549924623100619 := by
  unfold tailWord_366801
  simp only [CollatzResearch.WordTrace]
  refine ⟨13378331544150096468516257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8918887696100064312344171 13378331544150096468516257)
  ·
    refine ⟨10033748658112572351387193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13378331544150096468516257 10033748658112572351387193)
    ·
      refine ⟨7525311493584429263540395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10033748658112572351387193 7525311493584429263540395)
      ·
        refine ⟨11287967240376643895310593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7525311493584429263540395 11287967240376643895310593)
        ·
          refine ⟨8465975430282482921482945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11287967240376643895310593 8465975430282482921482945)
          ·
            refine ⟨6349481572711862191112209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8465975430282482921482945 6349481572711862191112209)
            ·
              refine ⟨4762111179533896643334157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6349481572711862191112209 4762111179533896643334157)
              ·
                refine ⟨1785791692325211241250309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4762111179533896643334157 1785791692325211241250309)
                ·
                  refine ⟨334835942310977107734433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1785791692325211241250309 334835942310977107734433)
                  ·
                    refine ⟨251126956733232830800825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334835942310977107734433 251126956733232830800825)
                    ·
                      refine ⟨188345217549924623100619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251126956733232830800825 188345217549924623100619)
                      ·
                        rfl

theorem cell23_366801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_366801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366801 prefixEnd_366801 := by exact prefixLift 366801
  have htrace : WordTrace (prefixWord ++ tailWord_366801) baseStart_366801 baseEnd_366801 := by
    simpa [prefixWord, tailWord_366801, baseEnd_366801] using wordTrace_append hprefix tailTrace_366801
  have hstable : (prefixWord ++ tailWord_366801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366801).length < 2 ^ (prefixWord ++ tailWord_366801).sum := by decide
  have hdescent : baseEnd_366801 < baseStart_366801 := by decide
  rcases family_descends (prefixWord ++ tailWord_366801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366807 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 7]
def baseStart_366807 : Nat := 118140960795 + 366807 * 2 ^ 59
def prefixEnd_366807 : Nat := 4983230072969 + 3 ^ 40 * 366807 * 2
def baseEnd_366807 : Nat := 20927588714872399958399

theorem tailTrace_366807 : CollatzResearch.WordTrace tailWord_366807 prefixEnd_366807 20927588714872399958399 := by
  unfold tailWord_366807
  simp only [CollatzResearch.WordTrace]
  refine ⟨13378550382128359493234675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8919033588085572995489783 13378550382128359493234675)
  ·
    refine ⟨20067825573192539239852013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13378550382128359493234675 20067825573192539239852013)
    ·
      refine ⟨7525434589947202214944505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20067825573192539239852013 7525434589947202214944505)
      ·
        refine ⟨5644075942460401661208379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7525434589947202214944505 5644075942460401661208379)
        ·
          refine ⟨8466113913690602491812569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5644075942460401661208379 8466113913690602491812569)
          ·
            refine ⟨6349585435267951868859427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8466113913690602491812569 6349585435267951868859427)
            ·
              refine ⟨9524378152901927803289141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349585435267951868859427 9524378152901927803289141)
              ·
                refine ⟨892910451834555731558357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9524378152901927803289141 892910451834555731558357)
                ·
                  refine ⟨20927588714872399958399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 892910451834555731558357 20927588714872399958399)
                  ·
                    rfl

theorem cell23_366807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 7].length) (baseStart_366807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366807 prefixEnd_366807 := by exact prefixLift 366807
  have htrace : WordTrace (prefixWord ++ tailWord_366807) baseStart_366807 baseEnd_366807 := by
    simpa [prefixWord, tailWord_366807, baseEnd_366807] using wordTrace_append hprefix tailTrace_366807
  have hstable : (prefixWord ++ tailWord_366807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366807).length < 2 ^ (prefixWord ++ tailWord_366807).sum := by decide
  have hdescent : baseEnd_366807 < baseStart_366807 := by decide
  rcases family_descends (prefixWord ++ tailWord_366807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366824 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 7]
def baseStart_366824 : Nat := 118140960795 + 366824 * 2 ^ 59
def prefixEnd_366824 : Nat := 4983230072969 + 3 ^ 40 * 366824 * 2
def baseEnd_366824 : Nat := 20928558622775337012557

theorem tailTrace_366824 : CollatzResearch.WordTrace tailWord_366824 prefixEnd_366824 20928558622775337012557 := by
  unfold tailWord_366824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689585211533385698301763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8919446948711180931069017 6689585211533385698301763)
  ·
    refine ⟨10034377817300078547452645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6689585211533385698301763 10034377817300078547452645)
    ·
      refine ⟨1881445840743764727647371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10034377817300078547452645 1881445840743764727647371)
      ·
        refine ⟨2822168761115647091471057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881445840743764727647371 2822168761115647091471057)
        ·
          refine ⟨2116626570836735318603293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2822168761115647091471057 2116626570836735318603293)
          ·
            refine ⟨793734964063775744476235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2116626570836735318603293 793734964063775744476235)
            ·
              refine ⟨1190602446095663616714353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793734964063775744476235 1190602446095663616714353)
              ·
                refine ⟨892951834571747712535765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190602446095663616714353 892951834571747712535765)
                ·
                  refine ⟨20928558622775337012557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 892951834571747712535765 20928558622775337012557)
                  ·
                    rfl

theorem cell23_366824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 7].length) (baseStart_366824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366824 prefixEnd_366824 := by exact prefixLift 366824
  have htrace : WordTrace (prefixWord ++ tailWord_366824) baseStart_366824 baseEnd_366824 := by
    simpa [prefixWord, tailWord_366824, baseEnd_366824] using wordTrace_append hprefix tailTrace_366824
  have hstable : (prefixWord ++ tailWord_366824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366824).length < 2 ^ (prefixWord ++ tailWord_366824).sum := by decide
  have hdescent : baseEnd_366824 < baseStart_366824 := by decide
  rcases family_descends (prefixWord ++ tailWord_366824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366852 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_366852 : Nat := 118140960795 + 366852 * 2 ^ 59
def prefixEnd_366852 : Nat := 4983230072969 + 3 ^ 40 * 366852 * 2
def baseEnd_366852 : Nat := 188371405063303923562885

theorem tailTrace_366852 : CollatzResearch.WordTrace tailWord_366852 prefixEnd_366852 188371405063303923562885 := by
  unfold tailWord_366852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690095833482666089311405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8920127777976888119081873 6690095833482666089311405)
  ·
    refine ⟨2508785937555999783491777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6690095833482666089311405 2508785937555999783491777)
    ·
      refine ⟨1881589453166999837618833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2508785937555999783491777 1881589453166999837618833)
      ·
        refine ⟨1411192089875249878214125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1881589453166999837618833 1411192089875249878214125)
        ·
          refine ⟨529197033703218704330297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1411192089875249878214125 529197033703218704330297)
          ·
            refine ⟨396897775277414028247723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529197033703218704330297 396897775277414028247723)
            ·
              refine ⟨595346662916121042371585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396897775277414028247723 595346662916121042371585)
              ·
                refine ⟨446509997187090781778689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595346662916121042371585 446509997187090781778689)
                ·
                  refine ⟨334882497890318086334017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446509997187090781778689 334882497890318086334017)
                  ·
                    refine ⟨251161873417738564750513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334882497890318086334017 251161873417738564750513)
                    ·
                      refine ⟨188371405063303923562885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251161873417738564750513 188371405063303923562885)
                      ·
                        rfl

theorem cell23_366852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_366852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366852 prefixEnd_366852 := by exact prefixLift 366852
  have htrace : WordTrace (prefixWord ++ tailWord_366852) baseStart_366852 baseEnd_366852 := by
    simpa [prefixWord, tailWord_366852, baseEnd_366852] using wordTrace_append hprefix tailTrace_366852
  have hstable : (prefixWord ++ tailWord_366852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366852).length < 2 ^ (prefixWord ++ tailWord_366852).sum := by decide
  have hdescent : baseEnd_366852 < baseStart_366852 := by decide
  rcases family_descends (prefixWord ++ tailWord_366852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366911 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 3]
def baseStart_366911 : Nat := 118140960795 + 366911 * 2 ^ 59
def prefixEnd_366911 : Nat := 4983230072969 + 3 ^ 40 * 366911 * 2
def baseEnd_366911 : Nat := 188401700421919192725113

theorem tailTrace_366911 : CollatzResearch.WordTrace tailWord_366911 prefixEnd_366911 188401700421919192725113 := by
  unfold tailWord_366911
  simp only [CollatzResearch.WordTrace]
  refine ⟨13382343573751585255020587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8921562382501056836680391 13382343573751585255020587)
  ·
    refine ⟨20073515360627377882530881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13382343573751585255020587 20073515360627377882530881)
    ·
      refine ⟨15055136520470533411898161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20073515360627377882530881 15055136520470533411898161)
      ·
        refine ⟨11291352390352900058923621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15055136520470533411898161 11291352390352900058923621)
        ·
          refine ⟨2117128573191168761048179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11291352390352900058923621 2117128573191168761048179)
          ·
            refine ⟨3175692859786753141572269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117128573191168761048179 3175692859786753141572269)
            ·
              refine ⟨1190884822420032428089601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3175692859786753141572269 1190884822420032428089601)
              ·
                refine ⟨893163616815024321067201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190884822420032428089601 893163616815024321067201)
                ·
                  refine ⟨669872712611268240800401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893163616815024321067201 669872712611268240800401)
                  ·
                    refine ⟨502404534458451180600301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 669872712611268240800401 502404534458451180600301)
                    ·
                      refine ⟨188401700421919192725113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 502404534458451180600301 188401700421919192725113)
                      ·
                        rfl

theorem cell23_366911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_366911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366911 prefixEnd_366911 := by exact prefixLift 366911
  have htrace : WordTrace (prefixWord ++ tailWord_366911) baseStart_366911 baseEnd_366911 := by
    simpa [prefixWord, tailWord_366911, baseEnd_366911] using wordTrace_append hprefix tailTrace_366911
  have hstable : (prefixWord ++ tailWord_366911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366911).length < 2 ^ (prefixWord ++ tailWord_366911).sum := by decide
  have hdescent : baseEnd_366911 < baseStart_366911 := by decide
  rcases family_descends (prefixWord ++ tailWord_366911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366981 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 2, 6, 2]
def baseStart_366981 : Nat := 118140960795 + 366981 * 2 ^ 59
def prefixEnd_366981 : Nat := 4983230072969 + 3 ^ 40 * 366981 * 2
def baseEnd_366981 : Nat := 188437644067733918849791

theorem tailTrace_366981 : CollatzResearch.WordTrace tailWord_366981 prefixEnd_366981 188437644067733918849791 := by
  unfold tailWord_366981
  simp only [CollatzResearch.WordTrace]
  refine ⟨13384896683497987210068797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8923264455665324806712531 13384896683497987210068797)
  ·
    refine ⟨5019336256311745203775799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13384896683497987210068797 5019336256311745203775799)
    ·
      refine ⟨7529004384467617805663699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5019336256311745203775799 7529004384467617805663699)
      ·
        refine ⟨11293506576701426708495549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7529004384467617805663699 11293506576701426708495549)
        ·
          refine ⟨4235064966263035015685831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11293506576701426708495549 4235064966263035015685831)
          ·
            refine ⟨6352597449394552523528747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235064966263035015685831 6352597449394552523528747)
            ·
              refine ⟨9528896174091828785293121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352597449394552523528747 9528896174091828785293121)
              ·
                refine ⟨7146672130568871588969841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9528896174091828785293121 7146672130568871588969841)
                ·
                  refine ⟨5360004097926653691727381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7146672130568871588969841 5360004097926653691727381)
                  ·
                    refine ⟨251250192090311891799721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5360004097926653691727381 251250192090311891799721)
                    ·
                      refine ⟨188437644067733918849791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251250192090311891799721 188437644067733918849791)
                      ·
                        rfl

theorem cell23_366981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_366981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_366981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_366981 prefixEnd_366981 := by exact prefixLift 366981
  have htrace : WordTrace (prefixWord ++ tailWord_366981) baseStart_366981 baseEnd_366981 := by
    simpa [prefixWord, tailWord_366981, baseEnd_366981] using wordTrace_append hprefix tailTrace_366981
  have hstable : (prefixWord ++ tailWord_366981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366981).length < 2 ^ (prefixWord ++ tailWord_366981).sum := by decide
  have hdescent : baseEnd_366981 < baseStart_366981 := by decide
  rcases family_descends (prefixWord ++ tailWord_366981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367001 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 3]
def baseStart_367001 : Nat := 118140960795 + 367001 * 2 ^ 59
def prefixEnd_367001 : Nat := 4983230072969 + 3 ^ 40 * 367001 * 2
def baseEnd_367001 : Nat := 188447913680823840599699

theorem tailTrace_367001 : CollatzResearch.WordTrace tailWord_367001 prefixEnd_367001 188447913680823840599699 := by
  unfold tailWord_367001
  simp only [CollatzResearch.WordTrace]
  refine ⟨13385626143425530625796857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8923750762283687083864571 13385626143425530625796857)
  ·
    refine ⟨10039219607569147969347643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13385626143425530625796857 10039219607569147969347643)
    ·
      refine ⟨15058829411353721954021465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10039219607569147969347643 15058829411353721954021465)
      ·
        refine ⟨11294122058515291465516099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15058829411353721954021465 11294122058515291465516099)
        ·
          refine ⟨16941183087772937198274149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11294122058515291465516099 16941183087772937198274149)
          ·
            refine ⟨3176471828957425724676403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16941183087772937198274149 3176471828957425724676403)
            ·
              refine ⟨4764707743436138587014605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176471828957425724676403 4764707743436138587014605)
              ·
                refine ⟨1786765403788551970130477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4764707743436138587014605 1786765403788551970130477)
                ·
                  refine ⟨670037026420706988798929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1786765403788551970130477 670037026420706988798929)
                  ·
                    refine ⟨502527769815530241599197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 670037026420706988798929 502527769815530241599197)
                    ·
                      refine ⟨188447913680823840599699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 502527769815530241599197 188447913680823840599699)
                      ·
                        rfl

theorem cell23_367001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_367001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367001 prefixEnd_367001 := by exact prefixLift 367001
  have htrace : WordTrace (prefixWord ++ tailWord_367001) baseStart_367001 baseEnd_367001 := by
    simpa [prefixWord, tailWord_367001, baseEnd_367001] using wordTrace_append hprefix tailTrace_367001
  have hstable : (prefixWord ++ tailWord_367001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367001).length < 2 ^ (prefixWord ++ tailWord_367001).sum := by decide
  have hdescent : baseEnd_367001 < baseStart_367001 := by decide
  rcases family_descends (prefixWord ++ tailWord_367001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367009 : List Nat := [1, 2, 3, 5, 1, 1, 2, 3, 1, 1, 3]
def baseStart_367009 : Nat := 118140960795 + 367009 * 2 ^ 59
def prefixEnd_367009 : Nat := 4983230072969 + 3 ^ 40 * 367009 * 2
def baseEnd_367009 : Nat := 188452021526059809299663

theorem tailTrace_367009 : CollatzResearch.WordTrace tailWord_367009 prefixEnd_367009 188452021526059809299663 := by
  unfold tailWord_367009
  simp only [CollatzResearch.WordTrace]
  refine ⟨13385917927396547992088081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8923945284931031994725387 13385917927396547992088081)
  ·
    refine ⟨10039438445547410994066061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13385917927396547992088081 10039438445547410994066061)
    ·
      refine ⟨3764789417080279122774773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10039438445547410994066061 3764789417080279122774773)
      ·
        refine ⟨352949007851276167760135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3764789417080279122774773 352949007851276167760135)
        ·
          refine ⟨529423511776914251640203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352949007851276167760135 529423511776914251640203)
          ·
            refine ⟨794135267665371377460305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529423511776914251640203 794135267665371377460305)
            ·
              refine ⟨595601450749028533095229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794135267665371377460305 595601450749028533095229)
              ·
                refine ⟨223350544030885699910711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595601450749028533095229 223350544030885699910711)
                ·
                  refine ⟨335025816046328549866067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223350544030885699910711 335025816046328549866067)
                  ·
                    refine ⟨502538724069492824799101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 335025816046328549866067 502538724069492824799101)
                    ·
                      refine ⟨188452021526059809299663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 502538724069492824799101 188452021526059809299663)
                      ·
                        rfl

theorem cell23_367009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_367009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367009 prefixEnd_367009 := by exact prefixLift 367009
  have htrace : WordTrace (prefixWord ++ tailWord_367009) baseStart_367009 baseEnd_367009 := by
    simpa [prefixWord, tailWord_367009, baseEnd_367009] using wordTrace_append hprefix tailTrace_367009
  have hstable : (prefixWord ++ tailWord_367009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367009).length < 2 ^ (prefixWord ++ tailWord_367009).sum := by decide
  have hdescent : baseEnd_367009 < baseStart_367009 := by decide
  rcases family_descends (prefixWord ++ tailWord_367009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367011 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4]
def baseStart_367011 : Nat := 118140960795 + 367011 * 2 ^ 59
def prefixEnd_367011 : Nat := 4983230072969 + 3 ^ 40 * 367011 * 2
def baseEnd_367011 : Nat := 188453048487368801474653

theorem tailTrace_367011 : CollatzResearch.WordTrace tailWord_367011 prefixEnd_367011 188453048487368801474653 := by
  unfold tailWord_367011
  simp only [CollatzResearch.WordTrace]
  refine ⟨13385990873389302333660887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8923993915592868222440591 13385990873389302333660887)
  ·
    refine ⟨20078986310083953500491331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13385990873389302333660887 20078986310083953500491331)
    ·
      refine ⟨30118479465125930250736997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20078986310083953500491331 30118479465125930250736997)
      ·
        refine ⟨5647214899711111922013187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30118479465125930250736997 5647214899711111922013187)
        ·
          refine ⟨8470822349566667883019781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5647214899711111922013187 8470822349566667883019781)
          ·
            refine ⟨1588279190543750228066209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8470822349566667883019781 1588279190543750228066209)
            ·
              refine ⟨1191209392907812671049657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588279190543750228066209 1191209392907812671049657)
              ·
                refine ⟨893407044680859503287243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191209392907812671049657 893407044680859503287243)
                ·
                  refine ⟨1340110567021289254930865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893407044680859503287243 1340110567021289254930865)
                  ·
                    refine ⟨1005082925265966941198149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340110567021289254930865 1005082925265966941198149)
                    ·
                      refine ⟨188453048487368801474653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1005082925265966941198149 188453048487368801474653)
                      ·
                        rfl

theorem cell23_367011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_367011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367011 prefixEnd_367011 := by exact prefixLift 367011
  have htrace : WordTrace (prefixWord ++ tailWord_367011) baseStart_367011 baseEnd_367011 := by
    simpa [prefixWord, tailWord_367011, baseEnd_367011] using wordTrace_append hprefix tailTrace_367011
  have hstable : (prefixWord ++ tailWord_367011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367011).length < 2 ^ (prefixWord ++ tailWord_367011).sum := by decide
  have hdescent : baseEnd_367011 < baseStart_367011 := by decide
  rcases family_descends (prefixWord ++ tailWord_367011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367015 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_367015 : Nat := 118140960795 + 367015 * 2 ^ 59
def prefixEnd_367015 : Nat := 4983230072969 + 3 ^ 40 * 367015 * 2
def baseEnd_367015 : Nat := 188455102409986785824635

theorem tailTrace_367015 : CollatzResearch.WordTrace tailWord_367015 prefixEnd_367015 188455102409986785824635 := by
  unfold tailWord_367015
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386136765374811016806499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8924091176916540677870999 13386136765374811016806499)
  ·
    refine ⟨20079205148062216525209749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13386136765374811016806499 20079205148062216525209749)
    ·
      refine ⟨941212741315416399619207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20079205148062216525209749 941212741315416399619207)
      ·
        refine ⟨1411819111973124599428811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941212741315416399619207 1411819111973124599428811)
        ·
          refine ⟨2117728667959686899143217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411819111973124599428811 2117728667959686899143217)
          ·
            refine ⟨1588296500969765174357413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117728667959686899143217 1588296500969765174357413)
            ·
              refine ⟨297805593931830970192015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1588296500969765174357413 297805593931830970192015)
              ·
                refine ⟨446708390897746455288023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297805593931830970192015 446708390897746455288023)
                ·
                  refine ⟨670062586346619682932035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446708390897746455288023 670062586346619682932035)
                  ·
                    refine ⟨1005093879519929524398053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 670062586346619682932035 1005093879519929524398053)
                    ·
                      refine ⟨188455102409986785824635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1005093879519929524398053 188455102409986785824635)
                      ·
                        rfl

theorem cell23_367015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_367015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367015 prefixEnd_367015 := by exact prefixLift 367015
  have htrace : WordTrace (prefixWord ++ tailWord_367015) baseStart_367015 baseEnd_367015 := by
    simpa [prefixWord, tailWord_367015, baseEnd_367015] using wordTrace_append hprefix tailTrace_367015
  have hstable : (prefixWord ++ tailWord_367015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367015).length < 2 ^ (prefixWord ++ tailWord_367015).sum := by decide
  have hdescent : baseEnd_367015 < baseStart_367015 := by decide
  rcases family_descends (prefixWord ++ tailWord_367015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367025 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 2, 4]
def baseStart_367025 : Nat := 118140960795 + 367025 * 2 ^ 59
def prefixEnd_367025 : Nat := 4983230072969 + 3 ^ 40 * 367025 * 2
def baseEnd_367025 : Nat := 62820079072177248899863

theorem tailTrace_367025 : CollatzResearch.WordTrace tailWord_367025 prefixEnd_367025 62820079072177248899863 := by
  unfold tailWord_367025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386501495338582724670529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8924334330225721816447019 13386501495338582724670529)
  ·
    refine ⟨10039876121503937043502897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13386501495338582724670529 10039876121503937043502897)
    ·
      refine ⟨7529907091127952782627173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10039876121503937043502897 7529907091127952782627173)
      ·
        refine ⟨1411857579586491146742595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7529907091127952782627173 1411857579586491146742595)
        ·
          refine ⟨2117786369379736720113893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411857579586491146742595 2117786369379736720113893)
          ·
            refine ⟨397084944258700635021355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2117786369379736720113893 397084944258700635021355)
            ·
              refine ⟨595627416388050952532033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397084944258700635021355 595627416388050952532033)
              ·
                refine ⟨446720562291038214399025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595627416388050952532033 446720562291038214399025)
                ·
                  refine ⟨335040421718278660799269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446720562291038214399025 335040421718278660799269)
                  ·
                    refine ⟨62820079072177248899863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 335040421718278660799269 62820079072177248899863)
                    ·
                      rfl

theorem cell23_367025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_367025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367025 prefixEnd_367025 := by exact prefixLift 367025
  have htrace : WordTrace (prefixWord ++ tailWord_367025) baseStart_367025 baseEnd_367025 := by
    simpa [prefixWord, tailWord_367025, baseEnd_367025] using wordTrace_append hprefix tailTrace_367025
  have hstable : (prefixWord ++ tailWord_367025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367025).length < 2 ^ (prefixWord ++ tailWord_367025).sum := by decide
  have hdescent : baseEnd_367025 < baseStart_367025 := by decide
  rcases family_descends (prefixWord ++ tailWord_367025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367034 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_367034 : Nat := 118140960795 + 367034 * 2 ^ 59
def prefixEnd_367034 : Nat := 4983230072969 + 3 ^ 40 * 367034 * 2
def baseEnd_367034 : Nat := 62821619514140737162349

theorem tailTrace_367034 : CollatzResearch.WordTrace tailWord_367034 prefixEnd_367034 62821619514140737162349 := by
  unfold tailWord_367034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346707438076494315437039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8924553168203984841165437 3346707438076494315437039)
  ·
    refine ⟨5020061157114741473155559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3346707438076494315437039 5020061157114741473155559)
    ·
      refine ⟨7530091735672112209733339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5020061157114741473155559 7530091735672112209733339)
      ·
        refine ⟨11295137603508168314600009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7530091735672112209733339 11295137603508168314600009)
        ·
          refine ⟨8471353202631126235950007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11295137603508168314600009 8471353202631126235950007)
          ·
            refine ⟨12707029803946689353925011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8471353202631126235950007 12707029803946689353925011)
            ·
              refine ⟨19060544705920034030887517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707029803946689353925011 19060544705920034030887517)
              ·
                refine ⟨7147704264720012761582819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19060544705920034030887517 7147704264720012761582819)
                ·
                  refine ⟨10721556397080019142374229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7147704264720012761582819 10721556397080019142374229)
                  ·
                    refine ⟨62821619514140737162349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 10721556397080019142374229 62821619514140737162349)
                    ·
                      rfl

theorem cell23_367034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_367034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367034 prefixEnd_367034 := by exact prefixLift 367034
  have htrace : WordTrace (prefixWord ++ tailWord_367034) baseStart_367034 baseEnd_367034 := by
    simpa [prefixWord, tailWord_367034, baseEnd_367034] using wordTrace_append hprefix tailTrace_367034
  have hstable : (prefixWord ++ tailWord_367034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367034).length < 2 ^ (prefixWord ++ tailWord_367034).sum := by decide
  have hdescent : baseEnd_367034 < baseStart_367034 := by decide
  rcases family_descends (prefixWord ++ tailWord_367034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367048 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_367048 : Nat := 118140960795 + 367048 * 2 ^ 59
def prefixEnd_367048 : Nat := 4983230072969 + 3 ^ 40 * 367048 * 2
def baseEnd_367048 : Nat := 188472047271585156711983

theorem tailTrace_367048 : CollatzResearch.WordTrace tailWord_367048 prefixEnd_367048 188472047271585156711983 := by
  unfold tailWord_367048
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693670187127628826378899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8924893582836838435171865 6693670187127628826378899)
  ·
    refine ⟨10040505280691443239568349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6693670187127628826378899 10040505280691443239568349)
    ·
      refine ⟨3765189480259291214838131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10040505280691443239568349 3765189480259291214838131)
      ·
        refine ⟨5647784220388936822257197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765189480259291214838131 5647784220388936822257197)
        ·
          refine ⟨2117919082645851308346449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5647784220388936822257197 2117919082645851308346449)
          ·
            refine ⟨1588439311984388481259837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117919082645851308346449 1588439311984388481259837)
            ·
              refine ⟨595664741994145680472439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1588439311984388481259837 595664741994145680472439)
              ·
                refine ⟨893497112991218520708659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595664741994145680472439 893497112991218520708659)
                ·
                  refine ⟨1340245669486827781062989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893497112991218520708659 1340245669486827781062989)
                  ·
                    refine ⟨502592126057560417898621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340245669486827781062989 502592126057560417898621)
                    ·
                      refine ⟨188472047271585156711983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 502592126057560417898621 188472047271585156711983)
                      ·
                        rfl

theorem cell23_367048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_367048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367048 prefixEnd_367048 := by exact prefixLift 367048
  have htrace : WordTrace (prefixWord ++ tailWord_367048) baseStart_367048 baseEnd_367048 := by
    simpa [prefixWord, tailWord_367048, baseEnd_367048] using wordTrace_append hprefix tailTrace_367048
  have hstable : (prefixWord ++ tailWord_367048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367048).length < 2 ^ (prefixWord ++ tailWord_367048).sum := by decide
  have hdescent : baseEnd_367048 < baseStart_367048 := by decide
  rcases family_descends (prefixWord ++ tailWord_367048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367061 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_367061 : Nat := 118140960795 + 367061 * 2 ^ 59
def prefixEnd_367061 : Nat := 4983230072969 + 3 ^ 40 * 367061 * 2
def baseEnd_367061 : Nat := 188478722520093605849423

theorem tailTrace_367061 : CollatzResearch.WordTrace tailWord_367061 prefixEnd_367061 188478722520093605849423 := by
  unfold tailWord_367061
  simp only [CollatzResearch.WordTrace]
  refine ⟨13387814523208160872981037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8925209682138773915320691 13387814523208160872981037)
  ·
    refine ⟨5020430446203060327367889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13387814523208160872981037 5020430446203060327367889)
    ·
      refine ⟨3765322834652295245525917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5020430446203060327367889 3765322834652295245525917)
      ·
        refine ⟨1411996062994610717072219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3765322834652295245525917 1411996062994610717072219)
        ·
          refine ⟨2117994094491916075608329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1411996062994610717072219 2117994094491916075608329)
          ·
            refine ⟨1588495570868937056706247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117994094491916075608329 1588495570868937056706247)
            ·
              refine ⟨2382743356303405585059371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588495570868937056706247 2382743356303405585059371)
              ·
                refine ⟨3574115034455108377589057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382743356303405585059371 3574115034455108377589057)
                ·
                  refine ⟨2680586275841331283191793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3574115034455108377589057 2680586275841331283191793)
                  ·
                    refine ⟨2010439706880998462393845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2680586275841331283191793 2010439706880998462393845)
                    ·
                      refine ⟨188478722520093605849423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2010439706880998462393845 188478722520093605849423)
                      ·
                        rfl

theorem cell23_367061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_367061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367061 prefixEnd_367061 := by exact prefixLift 367061
  have htrace : WordTrace (prefixWord ++ tailWord_367061) baseStart_367061 baseEnd_367061 := by
    simpa [prefixWord, tailWord_367061, baseEnd_367061] using wordTrace_append hprefix tailTrace_367061
  have hstable : (prefixWord ++ tailWord_367061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367061).length < 2 ^ (prefixWord ++ tailWord_367061).sum := by decide
  have hdescent : baseEnd_367061 < baseStart_367061 := by decide
  rcases family_descends (prefixWord ++ tailWord_367061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367091 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 3]
def baseStart_367091 : Nat := 118140960795 + 367091 * 2 ^ 59
def prefixEnd_367091 : Nat := 4983230072969 + 3 ^ 40 * 367091 * 2
def baseEnd_367091 : Nat := 188494126939728488474285

theorem tailTrace_367091 : CollatzResearch.WordTrace tailWord_367091 prefixEnd_367091 188494126939728488474285 := by
  unfold tailWord_367091
  simp only [CollatzResearch.WordTrace]
  refine ⟨13388908713099475996573127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8925939142066317331048751 13388908713099475996573127)
  ·
    refine ⟨20083363069649213994859691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13388908713099475996573127 20083363069649213994859691)
    ·
      refine ⟨30125044604473820992289537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20083363069649213994859691 30125044604473820992289537)
      ·
        refine ⟨22593783453355365744217153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30125044604473820992289537 22593783453355365744217153)
        ·
          refine ⟨16945337590016524308162865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22593783453355365744217153 16945337590016524308162865)
          ·
            refine ⟨12709003192512393231122149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16945337590016524308162865 12709003192512393231122149)
            ·
              refine ⟨2382938098596073730835403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12709003192512393231122149 2382938098596073730835403)
              ·
                refine ⟨3574407147894110596253105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382938098596073730835403 3574407147894110596253105)
                ·
                  refine ⟨2680805360920582947189829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3574407147894110596253105 2680805360920582947189829)
                  ·
                    refine ⟨502651005172609302598093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2680805360920582947189829 502651005172609302598093)
                    ·
                      refine ⟨188494126939728488474285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 502651005172609302598093 188494126939728488474285)
                      ·
                        rfl

theorem cell23_367091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_367091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367091 prefixEnd_367091 := by exact prefixLift 367091
  have htrace : WordTrace (prefixWord ++ tailWord_367091) baseStart_367091 baseEnd_367091 := by
    simpa [prefixWord, tailWord_367091, baseEnd_367091] using wordTrace_append hprefix tailTrace_367091
  have hstable : (prefixWord ++ tailWord_367091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367091).length < 2 ^ (prefixWord ++ tailWord_367091).sum := by decide
  have hdescent : baseEnd_367091 < baseStart_367091 := by decide
  rcases family_descends (prefixWord ++ tailWord_367091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367101 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_367101 : Nat := 118140960795 + 367101 * 2 ^ 59
def prefixEnd_367101 : Nat := 4983230072969 + 3 ^ 40 * 367101 * 2
def baseEnd_367101 : Nat := 188499261746273449349239

theorem tailTrace_367101 : CollatzResearch.WordTrace tailWord_367101 prefixEnd_367101 188499261746273449349239 := by
  unfold tailWord_367101
  simp only [CollatzResearch.WordTrace]
  refine ⟨13389273443063247704437157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8926182295375498469624771 13389273443063247704437157)
  ·
    refine ⟨2510488770574358944581967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13389273443063247704437157 2510488770574358944581967)
    ·
      refine ⟨3765733155861538416872951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510488770574358944581967 3765733155861538416872951)
      ·
        refine ⟨5648599733792307625309427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765733155861538416872951 5648599733792307625309427)
        ·
          refine ⟨8472899600688461437964141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648599733792307625309427 8472899600688461437964141)
          ·
            refine ⟨3177337350258173039236553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8472899600688461437964141 3177337350258173039236553)
            ·
              refine ⟨2383003012693629779427415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177337350258173039236553 2383003012693629779427415)
              ·
                refine ⟨3574504519040444669141123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383003012693629779427415 3574504519040444669141123)
                ·
                  refine ⟨5361756778560667003711685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574504519040444669141123 5361756778560667003711685)
                  ·
                    refine ⟨1005329395980125063195941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361756778560667003711685 1005329395980125063195941)
                    ·
                      refine ⟨188499261746273449349239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1005329395980125063195941 188499261746273449349239)
                      ·
                        rfl

theorem cell23_367101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_367101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367101 prefixEnd_367101 := by exact prefixLift 367101
  have htrace : WordTrace (prefixWord ++ tailWord_367101) baseStart_367101 baseEnd_367101 := by
    simpa [prefixWord, tailWord_367101, baseEnd_367101] using wordTrace_append hprefix tailTrace_367101
  have hstable : (prefixWord ++ tailWord_367101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367101).length < 2 ^ (prefixWord ++ tailWord_367101).sum := by decide
  have hdescent : baseEnd_367101 < baseStart_367101 := by decide
  rcases family_descends (prefixWord ++ tailWord_367101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367108 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_367108 : Nat := 118140960795 + 367108 * 2 ^ 59
def prefixEnd_367108 : Nat := 4983230072969 + 3 ^ 40 * 367108 * 2
def baseEnd_367108 : Nat := 188502856110854921961707

theorem tailTrace_367108 : CollatzResearch.WordTrace tailWord_367108 prefixEnd_367108 188502856110854921961707 := by
  unfold tailWord_367108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6694764377018943949970989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8926352502691925266627985 6694764377018943949970989)
  ·
    refine ⟨2510536641382103981239121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6694764377018943949970989 2510536641382103981239121)
    ·
      refine ⟨1882902481036577985929341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2510536641382103981239121 1882902481036577985929341)
      ·
        refine ⟨706088430388716744723503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1882902481036577985929341 706088430388716744723503)
        ·
          refine ⟨1059132645583075117085255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706088430388716744723503 1059132645583075117085255)
          ·
            refine ⟨1588698968374612675627883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059132645583075117085255 1588698968374612675627883)
            ·
              refine ⟨2383048452561919013441825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588698968374612675627883 2383048452561919013441825)
              ·
                refine ⟨1787286339421439260081369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2383048452561919013441825 1787286339421439260081369)
                ·
                  refine ⟨1340464754566079445061027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787286339421439260081369 1340464754566079445061027)
                  ·
                    refine ⟨2010697131849119167591541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1340464754566079445061027 2010697131849119167591541)
                    ·
                      refine ⟨188502856110854921961707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2010697131849119167591541 188502856110854921961707)
                      ·
                        rfl

theorem cell23_367108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_367108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367108 prefixEnd_367108 := by exact prefixLift 367108
  have htrace : WordTrace (prefixWord ++ tailWord_367108) baseStart_367108 baseEnd_367108 := by
    simpa [prefixWord, tailWord_367108, baseEnd_367108] using wordTrace_append hprefix tailTrace_367108
  have hstable : (prefixWord ++ tailWord_367108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367108).length < 2 ^ (prefixWord ++ tailWord_367108).sum := by decide
  have hdescent : baseEnd_367108 < baseStart_367108 := by decide
  rcases family_descends (prefixWord ++ tailWord_367108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367121 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_367121 : Nat := 118140960795 + 367121 * 2 ^ 59
def prefixEnd_367121 : Nat := 4983230072969 + 3 ^ 40 * 367121 * 2
def baseEnd_367121 : Nat := 188509531359363371099147

theorem tailTrace_367121 : CollatzResearch.WordTrace tailWord_367121 prefixEnd_367121 188509531359363371099147 := by
  unfold tailWord_367121
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390002902990791120165217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8926668601993860746776811 13390002902990791120165217)
  ·
    refine ⟨10042502177243093340123913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13390002902990791120165217 10042502177243093340123913)
    ·
      refine ⟨7531876632932320005092935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10042502177243093340123913 7531876632932320005092935)
      ·
        refine ⟨11297814949398480007639403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7531876632932320005092935 11297814949398480007639403)
        ·
          refine ⟨16946722424097720011459105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11297814949398480007639403 16946722424097720011459105)
          ·
            refine ⟨12710041818073290008594329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16946722424097720011459105 12710041818073290008594329)
            ·
              refine ⟨9532531363554967506445747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12710041818073290008594329 9532531363554967506445747)
              ·
                refine ⟨14298797045332451259668621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9532531363554967506445747 14298797045332451259668621)
                ·
                  refine ⟨5362048891999669222375733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14298797045332451259668621 5362048891999669222375733)
                  ·
                    refine ⟨502692083624968989597725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5362048891999669222375733 502692083624968989597725)
                    ·
                      refine ⟨188509531359363371099147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 502692083624968989597725 188509531359363371099147)
                      ·
                        rfl

theorem cell23_367121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_367121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367121 prefixEnd_367121 := by exact prefixLift 367121
  have htrace : WordTrace (prefixWord ++ tailWord_367121) baseStart_367121 baseEnd_367121 := by
    simpa [prefixWord, tailWord_367121, baseEnd_367121] using wordTrace_append hprefix tailTrace_367121
  have hstable : (prefixWord ++ tailWord_367121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367121).length < 2 ^ (prefixWord ++ tailWord_367121).sum := by decide
  have hdescent : baseEnd_367121 < baseStart_367121 := by decide
  rcases family_descends (prefixWord ++ tailWord_367121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367138 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_367138 : Nat := 118140960795 + 367138 * 2 ^ 59
def prefixEnd_367138 : Nat := 4983230072969 + 3 ^ 40 * 367138 * 2
def baseEnd_367138 : Nat := 188518260530489804586569

theorem tailTrace_367138 : CollatzResearch.WordTrace tailWord_367138 prefixEnd_367138 188518260530489804586569 := by
  unfold tailWord_367138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347655735982300755883517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8927081962619468682356045 3347655735982300755883517)
  ·
    refine ⟨1255370900993362783456319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3347655735982300755883517 1255370900993362783456319)
    ·
      refine ⟨1883056351490044175184479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1255370900993362783456319 1883056351490044175184479)
      ·
        refine ⟨2824584527235066262776719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883056351490044175184479 2824584527235066262776719)
        ·
          refine ⟨4236876790852599394165079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824584527235066262776719 4236876790852599394165079)
          ·
            refine ⟨6355315186278899091247619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236876790852599394165079 6355315186278899091247619)
            ·
              refine ⟨9532972779418348636871429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6355315186278899091247619 9532972779418348636871429)
              ·
                refine ⟨1787432396140940369413393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9532972779418348636871429 1787432396140940369413393)
                ·
                  refine ⟨1340574297105705277060045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787432396140940369413393 1340574297105705277060045)
                  ·
                    refine ⟨502715361414639478897517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1340574297105705277060045 502715361414639478897517)
                    ·
                      refine ⟨188518260530489804586569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 502715361414639478897517 188518260530489804586569)
                      ·
                        rfl

theorem cell23_367138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_367138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367138 prefixEnd_367138 := by exact prefixLift 367138
  have htrace : WordTrace (prefixWord ++ tailWord_367138) baseStart_367138 baseEnd_367138 := by
    simpa [prefixWord, tailWord_367138, baseEnd_367138] using wordTrace_append hprefix tailTrace_367138
  have hstable : (prefixWord ++ tailWord_367138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367138).length < 2 ^ (prefixWord ++ tailWord_367138).sum := by decide
  have hdescent : baseEnd_367138 < baseStart_367138 := by decide
  rcases family_descends (prefixWord ++ tailWord_367138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367175 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 2, 5]
def baseStart_367175 : Nat := 118140960795 + 367175 * 2 ^ 59
def prefixEnd_367175 : Nat := 4983230072969 + 3 ^ 40 * 367175 * 2
def baseEnd_367175 : Nat := 62845753104902053274633

theorem tailTrace_367175 : CollatzResearch.WordTrace tailWord_367175 prefixEnd_367175 62845753104902053274633 := by
  unfold tailWord_367175
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391972444795158342630979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8927981629863438895087319 13391972444795158342630979)
  ·
    refine ⟨20087958667192737513946469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13391972444795158342630979 20087958667192737513946469)
    ·
      refine ⟨3766492250098638283864963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20087958667192737513946469 3766492250098638283864963)
      ·
        refine ⟨5649738375147957425797445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766492250098638283864963 5649738375147957425797445)
        ·
          refine ⟨1059325945340242017337021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5649738375147957425797445 1059325945340242017337021)
          ·
            refine ⟨397247229502590756501383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1059325945340242017337021 397247229502590756501383)
            ·
              refine ⟨595870844253886134752075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397247229502590756501383 595870844253886134752075)
              ·
                refine ⟨893806266380829202128113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595870844253886134752075 893806266380829202128113)
                ·
                  refine ⟨670354699785621901596085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893806266380829202128113 670354699785621901596085)
                  ·
                    refine ⟨62845753104902053274633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 670354699785621901596085 62845753104902053274633)
                    ·
                      rfl

theorem cell23_367175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_367175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367175 prefixEnd_367175 := by exact prefixLift 367175
  have htrace : WordTrace (prefixWord ++ tailWord_367175) baseStart_367175 baseEnd_367175 := by
    simpa [prefixWord, tailWord_367175, baseEnd_367175] using wordTrace_append hprefix tailTrace_367175
  have hstable : (prefixWord ++ tailWord_367175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367175).length < 2 ^ (prefixWord ++ tailWord_367175).sum := by decide
  have hdescent : baseEnd_367175 < baseStart_367175 := by decide
  rcases family_descends (prefixWord ++ tailWord_367175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367178 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_367178 : Nat := 118140960795 + 367178 * 2 ^ 59
def prefixEnd_367178 : Nat := 4983230072969 + 3 ^ 40 * 367178 * 2
def baseEnd_367178 : Nat := 188538799756669648086385

theorem tailTrace_367178 : CollatzResearch.WordTrace tailWord_367178 prefixEnd_367178 188538799756669648086385 := by
  unfold tailWord_367178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348020465946072463747547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8928054575856193236660125 3348020465946072463747547)
  ·
    refine ⟨5022030698919108695621321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3348020465946072463747547 5022030698919108695621321)
    ·
      refine ⟨3766523024189331521715991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5022030698919108695621321 3766523024189331521715991)
      ·
        refine ⟨5649784536283997282573987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766523024189331521715991 5649784536283997282573987)
        ·
          refine ⟨8474676804425995923860981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649784536283997282573987 8474676804425995923860981)
          ·
            refine ⟨794500950414937117861967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8474676804425995923860981 794500950414937117861967)
            ·
              refine ⟨1191751425622405676792951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794500950414937117861967 1191751425622405676792951)
              ·
                refine ⟨1787627138433608515189427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191751425622405676792951 1787627138433608515189427)
                ·
                  refine ⟨2681440707650412772784141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787627138433608515189427 2681440707650412772784141)
                  ·
                    refine ⟨1005540265368904789794053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681440707650412772784141 1005540265368904789794053)
                    ·
                      refine ⟨188538799756669648086385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1005540265368904789794053 188538799756669648086385)
                      ·
                        rfl

theorem cell23_367178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_367178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367178 prefixEnd_367178 := by exact prefixLift 367178
  have htrace : WordTrace (prefixWord ++ tailWord_367178) baseStart_367178 baseEnd_367178 := by
    simpa [prefixWord, tailWord_367178, baseEnd_367178] using wordTrace_append hprefix tailTrace_367178
  have hstable : (prefixWord ++ tailWord_367178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367178).length < 2 ^ (prefixWord ++ tailWord_367178).sum := by decide
  have hdescent : baseEnd_367178 < baseStart_367178 := by decide
  rcases family_descends (prefixWord ++ tailWord_367178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367191 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_367191 : Nat := 118140960795 + 367191 * 2 ^ 59
def prefixEnd_367191 : Nat := 4983230072969 + 3 ^ 40 * 367191 * 2
def baseEnd_367191 : Nat := 188545475005178097223825

theorem tailTrace_367191 : CollatzResearch.WordTrace tailWord_367191 prefixEnd_367191 188545475005178097223825 := by
  unfold tailWord_367191
  simp only [CollatzResearch.WordTrace]
  refine ⟨13392556012737193075213427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8928370675158128716808951 13392556012737193075213427)
  ·
    refine ⟨20088834019105789612820141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13392556012737193075213427 20088834019105789612820141)
    ·
      refine ⟨7533312757164671104807553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20088834019105789612820141 7533312757164671104807553)
      ·
        refine ⟨5649984567873503328605665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7533312757164671104807553 5649984567873503328605665)
        ·
          refine ⟨4237488425905127496454249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5649984567873503328605665 4237488425905127496454249)
          ·
            refine ⟨3178116319428845622340687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4237488425905127496454249 3178116319428845622340687)
            ·
              refine ⟨4767174479143268433511031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178116319428845622340687 4767174479143268433511031)
              ·
                refine ⟨7150761718714902650266547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767174479143268433511031 7150761718714902650266547)
                ·
                  refine ⟨10726142578072353975399821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150761718714902650266547 10726142578072353975399821)
                  ·
                    refine ⟨4022303466777132740774933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10726142578072353975399821 4022303466777132740774933)
                    ·
                      refine ⟨188545475005178097223825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4022303466777132740774933 188545475005178097223825)
                      ·
                        rfl

theorem cell23_367191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_367191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367191 prefixEnd_367191 := by exact prefixLift 367191
  have htrace : WordTrace (prefixWord ++ tailWord_367191) baseStart_367191 baseEnd_367191 := by
    simpa [prefixWord, tailWord_367191, baseEnd_367191] using wordTrace_append hprefix tailTrace_367191
  have hstable : (prefixWord ++ tailWord_367191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367191).length < 2 ^ (prefixWord ++ tailWord_367191).sum := by decide
  have hdescent : baseEnd_367191 < baseStart_367191 := by decide
  rcases family_descends (prefixWord ++ tailWord_367191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367308 : List Nat := [2, 2, 1, 5, 1, 12]
def baseStart_367308 : Nat := 118140960795 + 367308 * 2 ^ 59
def prefixEnd_367308 : Nat := 4983230072969 + 3 ^ 40 * 367308 * 2
def baseEnd_367308 : Nat := 776154535974296870209

theorem tailTrace_367308 : CollatzResearch.WordTrace tailWord_367308 prefixEnd_367308 776154535974296870209 := by
  unfold tailWord_367308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6698411676656661028611289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8931215568875548038148385 6698411676656661028611289)
  ·
    refine ⟨5023808757492495771458467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6698411676656661028611289 5023808757492495771458467)
    ·
      refine ⟨7535713136238743657187701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5023808757492495771458467 7535713136238743657187701)
      ·
        refine ⟨706473106522382217861347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7535713136238743657187701 706473106522382217861347)
        ·
          refine ⟨1059709659783573326792021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706473106522382217861347 1059709659783573326792021)
          ·
            refine ⟨776154535974296870209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1059709659783573326792021 776154535974296870209)
            ·
              rfl

theorem cell23_367308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 12].length) (baseStart_367308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367308 prefixEnd_367308 := by exact prefixLift 367308
  have htrace : WordTrace (prefixWord ++ tailWord_367308) baseStart_367308 baseEnd_367308 := by
    simpa [prefixWord, tailWord_367308, baseEnd_367308] using wordTrace_append hprefix tailTrace_367308
  have hstable : (prefixWord ++ tailWord_367308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367308).length < 2 ^ (prefixWord ++ tailWord_367308).sum := by decide
  have hdescent : baseEnd_367308 < baseStart_367308 := by decide
  rcases family_descends (prefixWord ++ tailWord_367308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367338 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_367338 : Nat := 118140960795 + 367338 * 2 ^ 59
def prefixEnd_367338 : Nat := 4983230072969 + 3 ^ 40 * 367338 * 2
def baseEnd_367338 : Nat := 62873652220463007361883

theorem tailTrace_367338 : CollatzResearch.WordTrace tailWord_367338 prefixEnd_367338 62873652220463007361883 := by
  unfold tailWord_367338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349479385801159295203667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8931945028803091453876445 3349479385801159295203667)
  ·
    refine ⟨5024219078701738942805501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349479385801159295203667 5024219078701738942805501)
    ·
      refine ⟨1884082154513152103552063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5024219078701738942805501 1884082154513152103552063)
      ·
        refine ⟨2826123231769728155328095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884082154513152103552063 2826123231769728155328095)
        ·
          refine ⟨4239184847654592232992143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826123231769728155328095 4239184847654592232992143)
          ·
            refine ⟨6358777271481888349488215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239184847654592232992143 6358777271481888349488215)
            ·
              refine ⟨9538165907222832524232323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6358777271481888349488215 9538165907222832524232323)
              ·
                refine ⟨14307248860834248786348485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9538165907222832524232323 14307248860834248786348485)
                ·
                  refine ⟨2682609161406421647440341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14307248860834248786348485 2682609161406421647440341)
                  ·
                    refine ⟨62873652220463007361883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2682609161406421647440341 62873652220463007361883)
                    ·
                      rfl

theorem cell23_367338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_367338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367338 prefixEnd_367338 := by exact prefixLift 367338
  have htrace : WordTrace (prefixWord ++ tailWord_367338) baseStart_367338 baseEnd_367338 := by
    simpa [prefixWord, tailWord_367338, baseEnd_367338] using wordTrace_append hprefix tailTrace_367338
  have hstable : (prefixWord ++ tailWord_367338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367338).length < 2 ^ (prefixWord ++ tailWord_367338).sum := by decide
  have hdescent : baseEnd_367338 < baseStart_367338 := by decide
  rcases family_descends (prefixWord ++ tailWord_367338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367396 : List Nat := [2, 3, 1, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_367396 : Nat := 118140960795 + 367396 * 2 ^ 59
def prefixEnd_367396 : Nat := 4983230072969 + 3 ^ 40 * 367396 * 2
def baseEnd_367396 : Nat := 188650738539349795160383

theorem tailTrace_367396 : CollatzResearch.WordTrace tailWord_367396 prefixEnd_367396 188650738539349795160383 := by
  unfold tailWord_367396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6700016488497256543213021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8933355317996342057617361 6700016488497256543213021)
  ·
    refine ⟨2512506183186471203704883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6700016488497256543213021 2512506183186471203704883)
    ·
      refine ⟨3768759274779706805557325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2512506183186471203704883 3768759274779706805557325)
      ·
        refine ⟨1413284728042390052083997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3768759274779706805557325 1413284728042390052083997)
        ·
          refine ⟨529981773015896269531499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1413284728042390052083997 529981773015896269531499)
          ·
            refine ⟨794972659523844404297249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529981773015896269531499 794972659523844404297249)
            ·
              refine ⟨596229494642883303222937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794972659523844404297249 596229494642883303222937)
              ·
                refine ⟨447172120982162477417203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596229494642883303222937 447172120982162477417203)
                ·
                  refine ⟨670758181473243716125805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447172120982162477417203 670758181473243716125805)
                  ·
                    refine ⟨251534318052466393547177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 670758181473243716125805 251534318052466393547177)
                    ·
                      refine ⟨188650738539349795160383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251534318052466393547177 188650738539349795160383)
                      ·
                        rfl

theorem cell23_367396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_367396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367396 prefixEnd_367396 := by exact prefixLift 367396
  have htrace : WordTrace (prefixWord ++ tailWord_367396) baseStart_367396 baseEnd_367396 := by
    simpa [prefixWord, tailWord_367396, baseEnd_367396] using wordTrace_append hprefix tailTrace_367396
  have hstable : (prefixWord ++ tailWord_367396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367396).length < 2 ^ (prefixWord ++ tailWord_367396).sum := by decide
  have hdescent : baseEnd_367396 < baseStart_367396 := by decide
  rcases family_descends (prefixWord ++ tailWord_367396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367445 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_367445 : Nat := 118140960795 + 367445 * 2 ^ 59
def prefixEnd_367445 : Nat := 4983230072969 + 3 ^ 40 * 367445 * 2
def baseEnd_367445 : Nat := 62891966363806701149219

theorem tailTrace_367445 : CollatzResearch.WordTrace tailWord_367445 prefixEnd_367445 62891966363806701149219 := by
  unfold tailWord_367445
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401820153816994454959789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8934546769211329636639859 13401820153816994454959789)
  ·
    refine ⟨5025682557681372920609921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13401820153816994454959789 5025682557681372920609921)
    ·
      refine ⟨3769261918261029690457441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5025682557681372920609921 3769261918261029690457441)
      ·
        refine ⟨2826946438695772267843081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3769261918261029690457441 2826946438695772267843081)
        ·
          refine ⟨2120209829021829200882311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826946438695772267843081 2120209829021829200882311)
          ·
            refine ⟨3180314743532743801323467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120209829021829200882311 3180314743532743801323467)
            ·
              refine ⟨4770472115299115701985201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180314743532743801323467 4770472115299115701985201)
              ·
                refine ⟨3577854086474336776488901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770472115299115701985201 3577854086474336776488901)
                ·
                  refine ⟨670847641213938145591669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3577854086474336776488901 670847641213938145591669)
                  ·
                    refine ⟨62891966363806701149219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 670847641213938145591669 62891966363806701149219)
                    ·
                      rfl

theorem cell23_367445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_367445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367445 prefixEnd_367445 := by exact prefixLift 367445
  have htrace : WordTrace (prefixWord ++ tailWord_367445) baseStart_367445 baseEnd_367445 := by
    simpa [prefixWord, tailWord_367445, baseEnd_367445] using wordTrace_append hprefix tailTrace_367445
  have hstable : (prefixWord ++ tailWord_367445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367445).length < 2 ^ (prefixWord ++ tailWord_367445).sum := by decide
  have hdescent : baseEnd_367445 < baseStart_367445 := by decide
  rcases family_descends (prefixWord ++ tailWord_367445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367482 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2]
def baseStart_367482 : Nat := 118140960795 + 367482 * 2 ^ 59
def prefixEnd_367482 : Nat := 4983230072969 + 3 ^ 40 * 367482 * 2
def baseEnd_367482 : Nat := 188694897875636458684987

theorem tailTrace_367482 : CollatzResearch.WordTrace tailWord_367482 prefixEnd_367482 188694897875636458684987 := by
  unfold tailWord_367482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3350792413670737443514175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8935446436455299849371133 3350792413670737443514175)
  ·
    refine ⟨5026188620506106165271263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3350792413670737443514175 5026188620506106165271263)
    ·
      refine ⟨7539282930759159247906895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5026188620506106165271263 7539282930759159247906895)
      ·
        refine ⟨11308924396138738871860343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7539282930759159247906895 11308924396138738871860343)
        ·
          refine ⟨16963386594208108307790515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11308924396138738871860343 16963386594208108307790515)
          ·
            refine ⟨25445079891312162461685773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16963386594208108307790515 25445079891312162461685773)
            ·
              refine ⟨9541904959242060923132165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25445079891312162461685773 9541904959242060923132165)
              ·
                refine ⟨1789107179857886423087281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9541904959242060923132165 1789107179857886423087281)
                ·
                  refine ⟨1341830384893414817315461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1789107179857886423087281 1341830384893414817315461)
                  ·
                    refine ⟨251593197167515278246649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1341830384893414817315461 251593197167515278246649)
                    ·
                      refine ⟨188694897875636458684987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251593197167515278246649 188694897875636458684987)
                      ·
                        rfl

theorem cell23_367482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_367482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367482 prefixEnd_367482 := by exact prefixLift 367482
  have htrace : WordTrace (prefixWord ++ tailWord_367482) baseStart_367482 baseEnd_367482 := by
    simpa [prefixWord, tailWord_367482, baseEnd_367482] using wordTrace_append hprefix tailTrace_367482
  have hstable : (prefixWord ++ tailWord_367482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367482).length < 2 ^ (prefixWord ++ tailWord_367482).sum := by decide
  have hdescent : baseEnd_367482 < baseStart_367482 := by decide
  rcases family_descends (prefixWord ++ tailWord_367482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367492 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_367492 : Nat := 118140960795 + 367492 * 2 ^ 59
def prefixEnd_367492 : Nat := 4983230072969 + 3 ^ 40 * 367492 * 2
def baseEnd_367492 : Nat := 62900010894060473186647

theorem tailTrace_367492 : CollatzResearch.WordTrace tailWord_367492 prefixEnd_367492 62900010894060473186647 := by
  unfold tailWord_367492
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701767192323360740960365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8935689589764480987947153 6701767192323360740960365)
  ·
    refine ⟨2513162697121260277860137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6701767192323360740960365 2513162697121260277860137)
    ·
      refine ⟨1884872022840945208395103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2513162697121260277860137 1884872022840945208395103)
      ·
        refine ⟨2827308034261417812592655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884872022840945208395103 2827308034261417812592655)
        ·
          refine ⟨4240962051392126718888983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827308034261417812592655 4240962051392126718888983)
          ·
            refine ⟨6361443077088190078333475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240962051392126718888983 6361443077088190078333475)
            ·
              refine ⟨9542164615632285117500213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361443077088190078333475 9542164615632285117500213)
              ·
                refine ⟨894577932715526729765645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9542164615632285117500213 894577932715526729765645)
                ·
                  refine ⟨335466724768322523662117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894577932715526729765645 335466724768322523662117)
                  ·
                    refine ⟨62900010894060473186647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 335466724768322523662117 62900010894060473186647)
                    ·
                      rfl

theorem cell23_367492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_367492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367492 prefixEnd_367492 := by exact prefixLift 367492
  have htrace : WordTrace (prefixWord ++ tailWord_367492) baseStart_367492 baseEnd_367492 := by
    simpa [prefixWord, tailWord_367492, baseEnd_367492] using wordTrace_append hprefix tailTrace_367492
  have hstable : (prefixWord ++ tailWord_367492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367492).length < 2 ^ (prefixWord ++ tailWord_367492).sum := by decide
  have hdescent : baseEnd_367492 < baseStart_367492 := by decide
  rcases family_descends (prefixWord ++ tailWord_367492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367516 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_367516 : Nat := 118140960795 + 367516 * 2 ^ 59
def prefixEnd_367516 : Nat := 4983230072969 + 3 ^ 40 * 367516 * 2
def baseEnd_367516 : Nat := 188712356217889325659831

theorem tailTrace_367516 : CollatzResearch.WordTrace tailWord_367516 prefixEnd_367516 188712356217889325659831 := by
  unfold tailWord_367516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6702204868279886790397201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8936273157706515720529601 6702204868279886790397201)
  ·
    refine ⟨5026653651209915092797901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6702204868279886790397201 5026653651209915092797901)
    ·
      refine ⟨1884995119203718159799213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5026653651209915092797901 1884995119203718159799213)
      ·
        refine ⟨706873169701394309924705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1884995119203718159799213 706873169701394309924705)
        ·
          refine ⟨530154877276045732443529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706873169701394309924705 530154877276045732443529)
          ·
            refine ⟨397616157957034299332647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530154877276045732443529 397616157957034299332647)
            ·
              refine ⟨596424236935551448998971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397616157957034299332647 596424236935551448998971)
              ·
                refine ⟨894636355403327173498457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596424236935551448998971 894636355403327173498457)
                ·
                  refine ⟨670977266552495380123843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894636355403327173498457 670977266552495380123843)
                  ·
                    refine ⟨1006465899828743070185765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 670977266552495380123843 1006465899828743070185765)
                    ·
                      refine ⟨188712356217889325659831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1006465899828743070185765 188712356217889325659831)
                      ·
                        rfl

theorem cell23_367516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_367516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367516 prefixEnd_367516 := by exact prefixLift 367516
  have htrace : WordTrace (prefixWord ++ tailWord_367516) baseStart_367516 baseEnd_367516 := by
    simpa [prefixWord, tailWord_367516, baseEnd_367516] using wordTrace_append hprefix tailTrace_367516
  have hstable : (prefixWord ++ tailWord_367516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367516).length < 2 ^ (prefixWord ++ tailWord_367516).sum := by decide
  have hdescent : baseEnd_367516 < baseStart_367516 := by decide
  rcases family_descends (prefixWord ++ tailWord_367516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367519 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 3]
def baseStart_367519 : Nat := 118140960795 + 367519 * 2 ^ 59
def prefixEnd_367519 : Nat := 4983230072969 + 3 ^ 40 * 367519 * 2
def baseEnd_367519 : Nat := 188713896659852813922317

theorem tailTrace_367519 : CollatzResearch.WordTrace tailWord_367519 prefixEnd_367519 188713896659852813922317 := by
  unfold tailWord_367519
  simp only [CollatzResearch.WordTrace]
  refine ⟨13404519155548905093153611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8936346103699270062102407 13404519155548905093153611)
  ·
    refine ⟨20106778733323357639730417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13404519155548905093153611 20106778733323357639730417)
    ·
      refine ⟨15080084049992518229797813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20106778733323357639730417 15080084049992518229797813)
      ·
        refine ⟨1413757879686798584043545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15080084049992518229797813 1413757879686798584043545)
        ·
          refine ⟨1060318409765098938032659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1413757879686798584043545 1060318409765098938032659)
          ·
            refine ⟨1590477614647648407048989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060318409765098938032659 1590477614647648407048989)
            ·
              refine ⟨596429105492868152643371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1590477614647648407048989 596429105492868152643371)
              ·
                refine ⟨894643658239302228965057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596429105492868152643371 894643658239302228965057)
                ·
                  refine ⟨670982743679476671723793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894643658239302228965057 670982743679476671723793)
                  ·
                    refine ⟨503237057759607503792845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 670982743679476671723793 503237057759607503792845)
                    ·
                      refine ⟨188713896659852813922317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 503237057759607503792845 188713896659852813922317)
                      ·
                        rfl

theorem cell23_367519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_367519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367519 prefixEnd_367519 := by exact prefixLift 367519
  have htrace : WordTrace (prefixWord ++ tailWord_367519) baseStart_367519 baseEnd_367519 := by
    simpa [prefixWord, tailWord_367519, baseEnd_367519] using wordTrace_append hprefix tailTrace_367519
  have hstable : (prefixWord ++ tailWord_367519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367519).length < 2 ^ (prefixWord ++ tailWord_367519).sum := by decide
  have hdescent : baseEnd_367519 < baseStart_367519 := by decide
  rcases family_descends (prefixWord ++ tailWord_367519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367535 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 5, 5]
def baseStart_367535 : Nat := 118140960795 + 367535 * 2 ^ 59
def prefixEnd_367535 : Nat := 4983230072969 + 3 ^ 40 * 367535 * 2
def baseEnd_367535 : Nat := 62907370783441583774081

theorem tailTrace_367535 : CollatzResearch.WordTrace tailWord_367535 prefixEnd_367535 62907370783441583774081 := by
  unfold tailWord_367535
  simp only [CollatzResearch.WordTrace]
  refine ⟨13405102723490939825736059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8936735148993959883824039 13405102723490939825736059)
  ·
    refine ⟨20107654085236409738604089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13405102723490939825736059 20107654085236409738604089)
    ·
      refine ⟨15080740563927307303953067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20107654085236409738604089 15080740563927307303953067)
      ·
        refine ⟨22621110845890960955929601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15080740563927307303953067 22621110845890960955929601)
        ·
          refine ⟨16965833134418220716947201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22621110845890960955929601 16965833134418220716947201)
          ·
            refine ⟨12724374850813665537710401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16965833134418220716947201 12724374850813665537710401)
            ·
              refine ⟨9543281138110249153282801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12724374850813665537710401 9543281138110249153282801)
              ·
                refine ⟨7157460853582686864962101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9543281138110249153282801 7157460853582686864962101)
                ·
                  refine ⟨671011955023376893590197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7157460853582686864962101 671011955023376893590197)
                  ·
                    refine ⟨62907370783441583774081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 671011955023376893590197 62907370783441583774081)
                    ·
                      rfl

theorem cell23_367535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_367535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367535 prefixEnd_367535 := by exact prefixLift 367535
  have htrace : WordTrace (prefixWord ++ tailWord_367535) baseStart_367535 baseEnd_367535 := by
    simpa [prefixWord, tailWord_367535, baseEnd_367535] using wordTrace_append hprefix tailTrace_367535
  have hstable : (prefixWord ++ tailWord_367535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367535).length < 2 ^ (prefixWord ++ tailWord_367535).sum := by decide
  have hdescent : baseEnd_367535 < baseStart_367535 := by decide
  rcases family_descends (prefixWord ++ tailWord_367535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367586 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_367586 : Nat := 118140960795 + 367586 * 2 ^ 59
def prefixEnd_367586 : Nat := 4983230072969 + 3 ^ 40 * 367586 * 2
def baseEnd_367586 : Nat := 62916099954568017261503

theorem tailTrace_367586 : CollatzResearch.WordTrace tailWord_367586 prefixEnd_367586 62916099954568017261503 := by
  unfold tailWord_367586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351740711576543883960653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8937975230870783690561741 3351740711576543883960653)
  ·
    refine ⟨1256902766841203956485245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3351740711576543883960653 1256902766841203956485245)
    ·
      refine ⟨471338537565451483681967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1256902766841203956485245 471338537565451483681967)
      ·
        refine ⟨707007806348177225522951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471338537565451483681967 707007806348177225522951)
        ·
          refine ⟨1060511709522265838284427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707007806348177225522951 1060511709522265838284427)
          ·
            refine ⟨1590767564283398757426641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060511709522265838284427 1590767564283398757426641)
            ·
              refine ⟨1193075673212549068069981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590767564283398757426641 1193075673212549068069981)
              ·
                refine ⟨447403377454705900526243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193075673212549068069981 447403377454705900526243)
                ·
                  refine ⟨671105066182058850789365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447403377454705900526243 671105066182058850789365)
                  ·
                    refine ⟨62916099954568017261503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 671105066182058850789365 62916099954568017261503)
                    ·
                      rfl

theorem cell23_367586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_367586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367586 prefixEnd_367586 := by exact prefixLift 367586
  have htrace : WordTrace (prefixWord ++ tailWord_367586) baseStart_367586 baseEnd_367586 := by
    simpa [prefixWord, tailWord_367586, baseEnd_367586] using wordTrace_append hprefix tailTrace_367586
  have hstable : (prefixWord ++ tailWord_367586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367586).length < 2 ^ (prefixWord ++ tailWord_367586).sum := by decide
  have hdescent : baseEnd_367586 < baseStart_367586 := by decide
  rcases family_descends (prefixWord ++ tailWord_367586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367592 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_367592 : Nat := 118140960795 + 367592 * 2 ^ 59
def prefixEnd_367592 : Nat := 4983230072969 + 3 ^ 40 * 367592 * 2
def baseEnd_367592 : Nat := 188751380747631028309481

theorem tailTrace_367592 : CollatzResearch.WordTrace tailWord_367592 prefixEnd_367592 188751380747631028309481 := by
  unfold tailWord_367592
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703590842142219280280515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8938121122856292373707353 6703590842142219280280515)
  ·
    refine ⟨10055386263213328920420773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6703590842142219280280515 10055386263213328920420773)
    ·
      refine ⟨1885384924352499172578895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10055386263213328920420773 1885384924352499172578895)
      ·
        refine ⟨2828077386528748758868343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885384924352499172578895 2828077386528748758868343)
        ·
          refine ⟨4242116079793123138302515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828077386528748758868343 4242116079793123138302515)
          ·
            refine ⟨6363174119689684707453773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242116079793123138302515 6363174119689684707453773)
            ·
              refine ⟨2386190294883631765295165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6363174119689684707453773 2386190294883631765295165)
              ·
                refine ⟨894821360581361911985687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2386190294883631765295165 894821360581361911985687)
                ·
                  refine ⟨1342232040872042867978531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894821360581361911985687 1342232040872042867978531)
                  ·
                    refine ⟨2013348061308064301967797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1342232040872042867978531 2013348061308064301967797)
                    ·
                      refine ⟨188751380747631028309481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2013348061308064301967797 188751380747631028309481)
                      ·
                        rfl

theorem cell23_367592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_367592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367592 prefixEnd_367592 := by exact prefixLift 367592
  have htrace : WordTrace (prefixWord ++ tailWord_367592) baseStart_367592 baseEnd_367592 := by
    simpa [prefixWord, tailWord_367592, baseEnd_367592] using wordTrace_append hprefix tailTrace_367592
  have hstable : (prefixWord ++ tailWord_367592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367592).length < 2 ^ (prefixWord ++ tailWord_367592).sum := by decide
  have hdescent : baseEnd_367592 < baseStart_367592 := by decide
  rcases family_descends (prefixWord ++ tailWord_367592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367612 : List Nat := [2, 2, 2, 1, 2, 4, 2, 8]
def baseStart_367612 : Nat := 118140960795 + 367612 * 2 ^ 59
def prefixEnd_367612 : Nat := 4983230072969 + 3 ^ 40 * 367612 * 2
def baseEnd_367612 : Nat := 6991172235582257409607

theorem tailTrace_367612 : CollatzResearch.WordTrace tailWord_367612 prefixEnd_367612 6991172235582257409607 := by
  unfold tailWord_367612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703955572105990988144545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8938607429474654650859393 6703955572105990988144545)
  ·
    refine ⟨5027966679079493241108409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6703955572105990988144545 5027966679079493241108409)
    ·
      refine ⟨3770975009309619930831307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5027966679079493241108409 3770975009309619930831307)
      ·
        refine ⟨5656462513964429896246961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770975009309619930831307 5656462513964429896246961)
        ·
          refine ⟨4242346885473322422185221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656462513964429896246961 4242346885473322422185221)
          ·
            refine ⟨795440041026247954159729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4242346885473322422185221 795440041026247954159729)
            ·
              refine ⟨596580030769685965619797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795440041026247954159729 596580030769685965619797)
              ·
                refine ⟨6991172235582257409607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 596580030769685965619797 6991172235582257409607)
                ·
                  rfl

theorem cell23_367612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 8].length) (baseStart_367612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367612 prefixEnd_367612 := by exact prefixLift 367612
  have htrace : WordTrace (prefixWord ++ tailWord_367612) baseStart_367612 baseEnd_367612 := by
    simpa [prefixWord, tailWord_367612, baseEnd_367612] using wordTrace_append hprefix tailTrace_367612
  have hstable : (prefixWord ++ tailWord_367612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367612).length < 2 ^ (prefixWord ++ tailWord_367612).sum := by decide
  have hdescent : baseEnd_367612 < baseStart_367612 := by decide
  rcases family_descends (prefixWord ++ tailWord_367612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367626 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_367626 : Nat := 118140960795 + 367626 * 2 ^ 59
def prefixEnd_367626 : Nat := 4983230072969 + 3 ^ 40 * 367626 * 2
def baseEnd_367626 : Nat := 188768839089883895284325

theorem tailTrace_367626 : CollatzResearch.WordTrace tailWord_367626 prefixEnd_367626 188768839089883895284325 := by
  unfold tailWord_367626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352105441540315591824683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8938947844107508244865821 3352105441540315591824683)
  ·
    refine ⟨5028158162310473387737025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352105441540315591824683 5028158162310473387737025)
    ·
      refine ⟨3771118621732855040802769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5028158162310473387737025 3771118621732855040802769)
      ·
        refine ⟨2828338966299641280602077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3771118621732855040802769 2828338966299641280602077)
        ·
          refine ⟨1060627112362365480225779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2828338966299641280602077 1060627112362365480225779)
          ·
            refine ⟨1590940668543548220338669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060627112362365480225779 1590940668543548220338669)
            ·
              refine ⟨596602750703830582627001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1590940668543548220338669 596602750703830582627001)
              ·
                refine ⟨447452063027872936970251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596602750703830582627001 447452063027872936970251)
                ·
                  refine ⟨671178094541809405455377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447452063027872936970251 671178094541809405455377)
                  ·
                    refine ⟨503383570906357054091533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 671178094541809405455377 503383570906357054091533)
                    ·
                      refine ⟨188768839089883895284325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 503383570906357054091533 188768839089883895284325)
                      ·
                        rfl

theorem cell23_367626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_367626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367626 prefixEnd_367626 := by exact prefixLift 367626
  have htrace : WordTrace (prefixWord ++ tailWord_367626) baseStart_367626 baseEnd_367626 := by
    simpa [prefixWord, tailWord_367626, baseEnd_367626] using wordTrace_append hprefix tailTrace_367626
  have hstable : (prefixWord ++ tailWord_367626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367626).length < 2 ^ (prefixWord ++ tailWord_367626).sum := by decide
  have hdescent : baseEnd_367626 < baseStart_367626 := by decide
  rcases family_descends (prefixWord ++ tailWord_367626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367639 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_367639 : Nat := 118140960795 + 367639 * 2 ^ 59
def prefixEnd_367639 : Nat := 4983230072969 + 3 ^ 40 * 367639 * 2
def baseEnd_367639 : Nat := 188775514338392344421765

theorem tailTrace_367639 : CollatzResearch.WordTrace tailWord_367639 prefixEnd_367639 188775514338392344421765 := by
  unfold tailWord_367639
  simp only [CollatzResearch.WordTrace]
  refine ⟨13408895915114165587521971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8939263943409443725014647 13408895915114165587521971)
  ·
    refine ⟨20113343872671248381282957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13408895915114165587521971 20113343872671248381282957)
    ·
      refine ⟨7542503952251718142981109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20113343872671248381282957 7542503952251718142981109)
      ·
        refine ⟨707109745523598575904479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7542503952251718142981109 707109745523598575904479)
        ·
          refine ⟨1060664618285397863856719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707109745523598575904479 1060664618285397863856719)
          ·
            refine ⟨1590996927428096795785079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060664618285397863856719 1590996927428096795785079)
            ·
              refine ⟨2386495391142145193677619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590996927428096795785079 2386495391142145193677619)
              ·
                refine ⟨3579743086713217790516429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386495391142145193677619 3579743086713217790516429)
                ·
                  refine ⟨1342403657517456671443661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3579743086713217790516429 1342403657517456671443661)
                  ·
                    refine ⟨503401371569046251791373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1342403657517456671443661 503401371569046251791373)
                    ·
                      refine ⟨188775514338392344421765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 503401371569046251791373 188775514338392344421765)
                      ·
                        rfl

theorem cell23_367639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_367639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367639 prefixEnd_367639 := by exact prefixLift 367639
  have htrace : WordTrace (prefixWord ++ tailWord_367639) baseStart_367639 baseEnd_367639 := by
    simpa [prefixWord, tailWord_367639, baseEnd_367639] using wordTrace_append hprefix tailTrace_367639
  have hstable : (prefixWord ++ tailWord_367639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367639).length < 2 ^ (prefixWord ++ tailWord_367639).sum := by decide
  have hdescent : baseEnd_367639 < baseStart_367639 := by decide
  rcases family_descends (prefixWord ++ tailWord_367639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367672 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 1, 8]
def baseStart_367672 : Nat := 118140960795 + 367672 * 2 ^ 59
def prefixEnd_367672 : Nat := 4983230072969 + 3 ^ 40 * 367672 * 2
def baseEnd_367672 : Nat := 62930819733330238436371

theorem tailTrace_367672 : CollatzResearch.WordTrace tailWord_367672 prefixEnd_367672 62930819733330238436371 := by
  unfold tailWord_367672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705049761997306111736635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8940066349329741482315513 6705049761997306111736635)
  ·
    refine ⟨10057574642995959167604953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6705049761997306111736635 10057574642995959167604953)
    ·
      refine ⟨7543180982246969375703715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10057574642995959167604953 7543180982246969375703715)
      ·
        refine ⟨11314771473370454063555573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7543180982246969375703715 11314771473370454063555573)
        ·
          refine ⟨1060759825628480068458335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11314771473370454063555573 1060759825628480068458335)
          ·
            refine ⟨1591139738442720102687503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060759825628480068458335 1591139738442720102687503)
            ·
              refine ⟨2386709607664080154031255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591139738442720102687503 2386709607664080154031255)
              ·
                refine ⟨3580064411496120231046883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386709607664080154031255 3580064411496120231046883)
                ·
                  refine ⟨5370096617244180346570325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580064411496120231046883 5370096617244180346570325)
                  ·
                    refine ⟨62930819733330238436371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5370096617244180346570325 62930819733330238436371)
                    ·
                      rfl

theorem cell23_367672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_367672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367672 prefixEnd_367672 := by exact prefixLift 367672
  have htrace : WordTrace (prefixWord ++ tailWord_367672) baseStart_367672 baseEnd_367672 := by
    simpa [prefixWord, tailWord_367672, baseEnd_367672] using wordTrace_append hprefix tailTrace_367672
  have hstable : (prefixWord ++ tailWord_367672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367672).length < 2 ^ (prefixWord ++ tailWord_367672).sum := by decide
  have hdescent : baseEnd_367672 < baseStart_367672 := by decide
  rcases family_descends (prefixWord ++ tailWord_367672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367692 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_367692 : Nat := 118140960795 + 367692 * 2 ^ 59
def prefixEnd_367692 : Nat := 4983230072969 + 3 ^ 40 * 367692 * 2
def baseEnd_367692 : Nat := 188802728813080637059021

theorem tailTrace_367692 : CollatzResearch.WordTrace tailWord_367692 prefixEnd_367692 188802728813080637059021 := by
  unfold tailWord_367692
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705414491961077819600665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8940552655948103759467553 6705414491961077819600665)
  ·
    refine ⟨5029060868970808364700499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6705414491961077819600665 5029060868970808364700499)
    ·
      refine ⟨7543591303456212547050749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029060868970808364700499 7543591303456212547050749)
      ·
        refine ⟨2828846738796079705144031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7543591303456212547050749 2828846738796079705144031)
        ·
          refine ⟨4243270108194119557716047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828846738796079705144031 4243270108194119557716047)
          ·
            refine ⟨6364905162291179336574071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243270108194119557716047 6364905162291179336574071)
            ·
              refine ⟨9547357743436769004861107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364905162291179336574071 9547357743436769004861107)
              ·
                refine ⟨14321036615155153507291661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9547357743436769004861107 14321036615155153507291661)
                ·
                  refine ⟨5370388730683182565234373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14321036615155153507291661 5370388730683182565234373)
                  ·
                    refine ⟨1006947887003096730981445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5370388730683182565234373 1006947887003096730981445)
                    ·
                      refine ⟨188802728813080637059021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1006947887003096730981445 188802728813080637059021)
                      ·
                        rfl

theorem cell23_367692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_367692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367692 prefixEnd_367692 := by exact prefixLift 367692
  have htrace : WordTrace (prefixWord ++ tailWord_367692) baseStart_367692 baseEnd_367692 := by
    simpa [prefixWord, tailWord_367692, baseEnd_367692] using wordTrace_append hprefix tailTrace_367692
  have hstable : (prefixWord ++ tailWord_367692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367692).length < 2 ^ (prefixWord ++ tailWord_367692).sum := by decide
  have hdescent : baseEnd_367692 < baseStart_367692 := by decide
  rcases family_descends (prefixWord ++ tailWord_367692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367713 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_367713 : Nat := 118140960795 + 367713 * 2 ^ 59
def prefixEnd_367713 : Nat := 4983230072969 + 3 ^ 40 * 367713 * 2
def baseEnd_367713 : Nat := 188813511906825054896425

theorem tailTrace_367713 : CollatzResearch.WordTrace tailWord_367713 prefixEnd_367713 188813511906825054896425 := by
  unfold tailWord_367713
  simp only [CollatzResearch.WordTrace]
  refine ⟨13411594916846076225715793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8941063277897384150477195 13411594916846076225715793)
  ·
    refine ⟨10058696187634557169286845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13411594916846076225715793 10058696187634557169286845)
    ·
      refine ⟨3772011070362958938482567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10058696187634557169286845 3772011070362958938482567)
      ·
        refine ⟨5658016605544438407723851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772011070362958938482567 5658016605544438407723851)
        ·
          refine ⟨8487024908316657611585777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658016605544438407723851 8487024908316657611585777)
          ·
            refine ⟨6365268681237493208689333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8487024908316657611585777 6365268681237493208689333)
            ·
              refine ⟨596743938866014988314625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6365268681237493208689333 596743938866014988314625)
              ·
                refine ⟨447557954149511241235969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596743938866014988314625 447557954149511241235969)
                ·
                  refine ⟨335668465612133430926977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447557954149511241235969 335668465612133430926977)
                  ·
                    refine ⟨251751349209100073195233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 335668465612133430926977 251751349209100073195233)
                    ·
                      refine ⟨188813511906825054896425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251751349209100073195233 188813511906825054896425)
                      ·
                        rfl

theorem cell23_367713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_367713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367713 prefixEnd_367713 := by exact prefixLift 367713
  have htrace : WordTrace (prefixWord ++ tailWord_367713) baseStart_367713 baseEnd_367713 := by
    simpa [prefixWord, tailWord_367713, baseEnd_367713] using wordTrace_append hprefix tailTrace_367713
  have hstable : (prefixWord ++ tailWord_367713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367713).length < 2 ^ (prefixWord ++ tailWord_367713).sum := by decide
  have hdescent : baseEnd_367713 < baseStart_367713 := by decide
  rcases family_descends (prefixWord ++ tailWord_367713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367719 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 7]
def baseStart_367719 : Nat := 118140960795 + 367719 * 2 ^ 59
def prefixEnd_367719 : Nat := 4983230072969 + 3 ^ 40 * 367719 * 2
def baseEnd_367719 : Nat := 20979621421194670157933

theorem tailTrace_367719 : CollatzResearch.WordTrace tailWord_367719 prefixEnd_367719 20979621421194670157933 := by
  unfold tailWord_367719
  simp only [CollatzResearch.WordTrace]
  refine ⟨13411813754824339250434211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8941209169882892833622807 13411813754824339250434211)
  ·
    refine ⟨20117720632236508875651317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13411813754824339250434211 20117720632236508875651317)
    ·
      refine ⟨1886036309272172707092311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20117720632236508875651317 1886036309272172707092311)
      ·
        refine ⟨2829054463908259060638467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886036309272172707092311 2829054463908259060638467)
        ·
          refine ⟨4243581695862388590957701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829054463908259060638467 4243581695862388590957701)
          ·
            refine ⟨795671567974197860804569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4243581695862388590957701 795671567974197860804569)
            ·
              refine ⟨596753675980648395603427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795671567974197860804569 596753675980648395603427)
              ·
                refine ⟨895130513970972593405141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596753675980648395603427 895130513970972593405141)
                ·
                  refine ⟨20979621421194670157933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 895130513970972593405141 20979621421194670157933)
                  ·
                    rfl

theorem cell23_367719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 7].length) (baseStart_367719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367719 prefixEnd_367719 := by exact prefixLift 367719
  have htrace : WordTrace (prefixWord ++ tailWord_367719) baseStart_367719 baseEnd_367719 := by
    simpa [prefixWord, tailWord_367719, baseEnd_367719] using wordTrace_append hprefix tailTrace_367719
  have hstable : (prefixWord ++ tailWord_367719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367719).length < 2 ^ (prefixWord ++ tailWord_367719).sum := by decide
  have hdescent : baseEnd_367719 < baseStart_367719 := by decide
  rcases family_descends (prefixWord ++ tailWord_367719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367730 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_367730 : Nat := 118140960795 + 367730 * 2 ^ 59
def prefixEnd_367730 : Nat := 4983230072969 + 3 ^ 40 * 367730 * 2
def baseEnd_367730 : Nat := 188822241077951488383847

theorem tailTrace_367730 : CollatzResearch.WordTrace tailWord_367730 prefixEnd_367730 188822241077951488383847 := by
  unfold tailWord_367730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353053739446122032271161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8941476638522992086056429 3353053739446122032271161)
  ·
    refine ⟨2514790304584591524203371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3353053739446122032271161 2514790304584591524203371)
    ·
      refine ⟨3772185456876887286305057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2514790304584591524203371 3772185456876887286305057)
      ·
        refine ⟨2829139092657665464728793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3772185456876887286305057 2829139092657665464728793)
        ·
          refine ⟨2121854319493249098546595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2829139092657665464728793 2121854319493249098546595)
          ·
            refine ⟨3182781479239873647819893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121854319493249098546595 3182781479239873647819893)
            ·
              refine ⟨298385763678738154483115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3182781479239873647819893 298385763678738154483115)
              ·
                refine ⟨447578645518107231724673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298385763678738154483115 447578645518107231724673)
                ·
                  refine ⟨335683984138580423793505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447578645518107231724673 335683984138580423793505)
                  ·
                    refine ⟨251762988103935317845129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 335683984138580423793505 251762988103935317845129)
                    ·
                      refine ⟨188822241077951488383847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251762988103935317845129 188822241077951488383847)
                      ·
                        rfl

theorem cell23_367730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_367730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367730 prefixEnd_367730 := by exact prefixLift 367730
  have htrace : WordTrace (prefixWord ++ tailWord_367730) baseStart_367730 baseEnd_367730 := by
    simpa [prefixWord, tailWord_367730, baseEnd_367730] using wordTrace_append hprefix tailTrace_367730
  have hstable : (prefixWord ++ tailWord_367730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367730).length < 2 ^ (prefixWord ++ tailWord_367730).sum := by decide
  have hdescent : baseEnd_367730 < baseStart_367730 := by decide
  rcases family_descends (prefixWord ++ tailWord_367730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367739 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 2, 5, 2]
def baseStart_367739 : Nat := 118140960795 + 367739 * 2 ^ 59
def prefixEnd_367739 : Nat := 4983230072969 + 3 ^ 40 * 367739 * 2
def baseEnd_367739 : Nat := 188826862403841953171305

theorem tailTrace_367739 : CollatzResearch.WordTrace tailWord_367739 prefixEnd_367739 188826862403841953171305 := by
  unfold tailWord_367739
  simp only [CollatzResearch.WordTrace]
  refine ⟨13412543214751882666162271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8941695476501255110774847 13412543214751882666162271)
  ·
    refine ⟨20118814822127823999243407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13412543214751882666162271 20118814822127823999243407)
    ·
      refine ⟨30178222233191735998865111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20118814822127823999243407 30178222233191735998865111)
      ·
        refine ⟨45267333349787603998297667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30178222233191735998865111 45267333349787603998297667)
        ·
          refine ⟨67901000024681405997446501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45267333349787603998297667 67901000024681405997446501)
          ·
            refine ⟨12731437504627763624521219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67901000024681405997446501 12731437504627763624521219)
            ·
              refine ⟨19097156256941645436781829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12731437504627763624521219 19097156256941645436781829)
              ·
                refine ⟨3580716798176558519396593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19097156256941645436781829 3580716798176558519396593)
                ·
                  refine ⟨2685537598632418889547445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580716798176558519396593 2685537598632418889547445)
                  ·
                    refine ⟨251769149871789270895073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2685537598632418889547445 251769149871789270895073)
                    ·
                      refine ⟨188826862403841953171305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251769149871789270895073 188826862403841953171305)
                      ·
                        rfl

theorem cell23_367739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5, 2].length) (baseStart_367739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367739 prefixEnd_367739 := by exact prefixLift 367739
  have htrace : WordTrace (prefixWord ++ tailWord_367739) baseStart_367739 baseEnd_367739 := by
    simpa [prefixWord, tailWord_367739, baseEnd_367739] using wordTrace_append hprefix tailTrace_367739
  have hstable : (prefixWord ++ tailWord_367739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367739).length < 2 ^ (prefixWord ++ tailWord_367739).sum := by decide
  have hdescent : baseEnd_367739 < baseStart_367739 := by decide
  rcases family_descends (prefixWord ++ tailWord_367739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367826 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 6]
def baseStart_367826 : Nat := 118140960795 + 367826 * 2 ^ 59
def prefixEnd_367826 : Nat := 4983230072969 + 3 ^ 40 * 367826 * 2
def baseEnd_367826 : Nat := 20985726135642568087045

theorem tailTrace_367826 : CollatzResearch.WordTrace tailWord_367826 prefixEnd_367826 20985726135642568087045 := by
  unfold tailWord_367826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353929091359174131144833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8943810910291131016386221 3353929091359174131144833)
  ·
    refine ⟨2515446818519380598358625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3353929091359174131144833 2515446818519380598358625)
    ·
      refine ⟨1886585113889535448768969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2515446818519380598358625 1886585113889535448768969)
      ·
        refine ⟨1414938835417151586576727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1886585113889535448768969 1414938835417151586576727)
        ·
          refine ⟨2122408253125727379865091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414938835417151586576727 2122408253125727379865091)
          ·
            refine ⟨3183612379688591069797637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122408253125727379865091 3183612379688591069797637)
            ·
              refine ⟨596927321191610825587057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3183612379688591069797637 596927321191610825587057)
              ·
                refine ⟨447695490893708119190293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596927321191610825587057 447695490893708119190293)
                ·
                  refine ⟨20985726135642568087045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 447695490893708119190293 20985726135642568087045)
                  ·
                    rfl

theorem cell23_367826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_367826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367826 prefixEnd_367826 := by exact prefixLift 367826
  have htrace : WordTrace (prefixWord ++ tailWord_367826) baseStart_367826 baseEnd_367826 := by
    simpa [prefixWord, tailWord_367826, baseEnd_367826] using wordTrace_append hprefix tailTrace_367826
  have hstable : (prefixWord ++ tailWord_367826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367826).length < 2 ^ (prefixWord ++ tailWord_367826).sum := by decide
  have hdescent : baseEnd_367826 < baseStart_367826 := by decide
  rcases family_descends (prefixWord ++ tailWord_367826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367839 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 3, 5]
def baseStart_367839 : Nat := 118140960795 + 367839 * 2 ^ 59
def prefixEnd_367839 : Nat := 4983230072969 + 3 ^ 40 * 367839 * 2
def baseEnd_367839 : Nat := 62959403489763853973615

theorem tailTrace_367839 : CollatzResearch.WordTrace tailWord_367839 prefixEnd_367839 62959403489763853973615 := by
  unfold tailWord_367839
  simp only [CollatzResearch.WordTrace]
  refine ⟨13416190514389599744802571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8944127009593066496535047 13416190514389599744802571)
  ·
    refine ⟨20124285771584399617203857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13416190514389599744802571 20124285771584399617203857)
    ·
      refine ⟨15093214328688299712902893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20124285771584399617203857 15093214328688299712902893)
      ·
        refine ⟨5659955373258112392338585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15093214328688299712902893 5659955373258112392338585)
        ·
          refine ⟨4244966529943584294253939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5659955373258112392338585 4244966529943584294253939)
          ·
            refine ⟨6367449794915376441380909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244966529943584294253939 6367449794915376441380909)
            ·
              refine ⟨2387793673093266165517841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6367449794915376441380909 2387793673093266165517841)
              ·
                refine ⟨1790845254819949624138381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2387793673093266165517841 1790845254819949624138381)
                ·
                  refine ⟨671566970557481109051893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1790845254819949624138381 671566970557481109051893)
                  ·
                    refine ⟨62959403489763853973615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 671566970557481109051893 62959403489763853973615)
                    ·
                      rfl

theorem cell23_367839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_367839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367839 prefixEnd_367839 := by exact prefixLift 367839
  have htrace : WordTrace (prefixWord ++ tailWord_367839) baseStart_367839 baseEnd_367839 := by
    simpa [prefixWord, tailWord_367839, baseEnd_367839] using wordTrace_append hprefix tailTrace_367839
  have hstable : (prefixWord ++ tailWord_367839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367839).length < 2 ^ (prefixWord ++ tailWord_367839).sum := by decide
  have hdescent : baseEnd_367839 < baseStart_367839 := by decide
  rcases family_descends (prefixWord ++ tailWord_367839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367853 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_367853 : Nat := 118140960795 + 367853 * 2 ^ 59
def prefixEnd_367853 : Nat := 4983230072969 + 3 ^ 40 * 367853 * 2
def baseEnd_367853 : Nat := 188885399198454507145781

theorem tailTrace_367853 : CollatzResearch.WordTrace tailWord_367853 prefixEnd_367853 188885399198454507145781 := by
  unfold tailWord_367853
  simp only [CollatzResearch.WordTrace]
  refine ⟨13416701136338880135812213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8944467424225920090541475 13416701136338880135812213)
  ·
    refine ⟨1257815731531770012732395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13416701136338880135812213 1257815731531770012732395)
    ·
      refine ⟨1886723597297655019098593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1257815731531770012732395 1886723597297655019098593)
      ·
        refine ⟨1415042697973241264323945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1886723597297655019098593 1415042697973241264323945)
        ·
          refine ⟨1061282023479930948242959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415042697973241264323945 1061282023479930948242959)
          ·
            refine ⟨1591923035219896422364439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061282023479930948242959 1591923035219896422364439)
            ·
              refine ⟨2387884552829844633546659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591923035219896422364439 2387884552829844633546659)
              ·
                refine ⟨3581826829244766950319989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387884552829844633546659 3581826829244766950319989)
                ·
                  refine ⟨335796265241696901592499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3581826829244766950319989 335796265241696901592499)
                  ·
                    refine ⟨503694397862545352388749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 335796265241696901592499 503694397862545352388749)
                    ·
                      refine ⟨188885399198454507145781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 503694397862545352388749 188885399198454507145781)
                      ·
                        rfl

theorem cell23_367853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_367853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367853 prefixEnd_367853 := by exact prefixLift 367853
  have htrace : WordTrace (prefixWord ++ tailWord_367853) baseStart_367853 baseEnd_367853 := by
    simpa [prefixWord, tailWord_367853, baseEnd_367853] using wordTrace_append hprefix tailTrace_367853
  have hstable : (prefixWord ++ tailWord_367853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367853).length < 2 ^ (prefixWord ++ tailWord_367853).sum := by decide
  have hdescent : baseEnd_367853 < baseStart_367853 := by decide
  rcases family_descends (prefixWord ++ tailWord_367853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367873 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 1, 5]
def baseStart_367873 : Nat := 118140960795 + 367873 * 2 ^ 59
def prefixEnd_367873 : Nat := 4983230072969 + 3 ^ 40 * 367873 * 2
def baseEnd_367873 : Nat := 62965222937181476298563

theorem tailTrace_367873 : CollatzResearch.WordTrace tailWord_367873 prefixEnd_367873 62965222937181476298563 := by
  unfold tailWord_367873
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417430596266423551540273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8944953730844282367693515 13417430596266423551540273)
  ·
    refine ⟨10063072947199817663655205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13417430596266423551540273 10063072947199817663655205)
    ·
      refine ⟨1886826177599965811935351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10063072947199817663655205 1886826177599965811935351)
      ·
        refine ⟨2830239266399948717903027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886826177599965811935351 2830239266399948717903027)
        ·
          refine ⟨4245358899599923076854541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830239266399948717903027 4245358899599923076854541)
          ·
            refine ⟨1592009587349971153820453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4245358899599923076854541 1592009587349971153820453)
            ·
              refine ⟨298501797628119591341335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1592009587349971153820453 298501797628119591341335)
              ·
                refine ⟨447752696442179387012003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298501797628119591341335 447752696442179387012003)
                ·
                  refine ⟨671629044663269080518005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447752696442179387012003 671629044663269080518005)
                  ·
                    refine ⟨62965222937181476298563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 671629044663269080518005 62965222937181476298563)
                    ·
                      rfl

theorem cell23_367873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_367873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367873 prefixEnd_367873 := by exact prefixLift 367873
  have htrace : WordTrace (prefixWord ++ tailWord_367873) baseStart_367873 baseEnd_367873 := by
    simpa [prefixWord, tailWord_367873, baseEnd_367873] using wordTrace_append hprefix tailTrace_367873
  have hstable : (prefixWord ++ tailWord_367873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367873).length < 2 ^ (prefixWord ++ tailWord_367873).sum := by decide
  have hdescent : baseEnd_367873 < baseStart_367873 := by decide
  rcases family_descends (prefixWord ++ tailWord_367873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367889 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_367889 : Nat := 118140960795 + 367889 * 2 ^ 59
def prefixEnd_367889 : Nat := 4983230072969 + 3 ^ 40 * 367889 * 2
def baseEnd_367889 : Nat := 188903884502016366295615

theorem tailTrace_367889 : CollatzResearch.WordTrace tailWord_367889 prefixEnd_367889 188903884502016366295615 := by
  unfold tailWord_367889
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418014164208458284122721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8945342776138972189415147 13418014164208458284122721)
  ·
    refine ⟨10063510623156343713092041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13418014164208458284122721 10063510623156343713092041)
    ·
      refine ⟨7547632967367257784819031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10063510623156343713092041 7547632967367257784819031)
      ·
        refine ⟨11321449451050886677228547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7547632967367257784819031 11321449451050886677228547)
        ·
          refine ⟨16982174176576330015842821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11321449451050886677228547 16982174176576330015842821)
          ·
            refine ⟨3184157658108061877970529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16982174176576330015842821 3184157658108061877970529)
            ·
              refine ⟨2388118243581046408477897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184157658108061877970529 2388118243581046408477897)
              ·
                refine ⟨1791088682685784806358423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388118243581046408477897 1791088682685784806358423)
                ·
                  refine ⟨2686633024028677209537635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791088682685784806358423 2686633024028677209537635)
                  ·
                    refine ⟨4029949536043015814306453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686633024028677209537635 4029949536043015814306453)
                    ·
                      refine ⟨188903884502016366295615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4029949536043015814306453 188903884502016366295615)
                      ·
                        rfl

theorem cell23_367889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_367889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367889 prefixEnd_367889 := by exact prefixLift 367889
  have htrace : WordTrace (prefixWord ++ tailWord_367889) baseStart_367889 baseEnd_367889 := by
    simpa [prefixWord, tailWord_367889, baseEnd_367889] using wordTrace_append hprefix tailTrace_367889
  have hstable : (prefixWord ++ tailWord_367889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367889).length < 2 ^ (prefixWord ++ tailWord_367889).sum := by decide
  have hdescent : baseEnd_367889 < baseStart_367889 := by decide
  rcases family_descends (prefixWord ++ tailWord_367889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367896 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_367896 : Nat := 118140960795 + 367896 * 2 ^ 59
def prefixEnd_367896 : Nat := 4983230072969 + 3 ^ 40 * 367896 * 2
def baseEnd_367896 : Nat := 188907478866597838908083

theorem tailTrace_367896 : CollatzResearch.WordTrace tailWord_367896 prefixEnd_367896 188907478866597838908083 := by
  unfold tailWord_367896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709134737591549239813771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8945512983455398986418361 6709134737591549239813771)
  ·
    refine ⟨10063702106387323859720657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6709134737591549239813771 10063702106387323859720657)
    ·
      refine ⟨7547776579790492894790493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10063702106387323859720657 7547776579790492894790493)
      ·
        refine ⟨2830416217421434835546435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7547776579790492894790493 2830416217421434835546435)
        ·
          refine ⟨4245624326132152253319653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830416217421434835546435 4245624326132152253319653)
          ·
            refine ⟨796054561149778547497435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4245624326132152253319653 796054561149778547497435)
            ·
              refine ⟨1194081841724667821246153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796054561149778547497435 1194081841724667821246153)
              ·
                refine ⟨895561381293500865934615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194081841724667821246153 895561381293500865934615)
                ·
                  refine ⟨1343342071940251298901923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895561381293500865934615 1343342071940251298901923)
                  ·
                    refine ⟨2015013107910376948352885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1343342071940251298901923 2015013107910376948352885)
                    ·
                      refine ⟨188907478866597838908083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2015013107910376948352885 188907478866597838908083)
                      ·
                        rfl

theorem cell23_367896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_367896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367896 prefixEnd_367896 := by exact prefixLift 367896
  have htrace : WordTrace (prefixWord ++ tailWord_367896) baseStart_367896 baseEnd_367896 := by
    simpa [prefixWord, tailWord_367896, baseEnd_367896] using wordTrace_append hprefix tailTrace_367896
  have hstable : (prefixWord ++ tailWord_367896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367896).length < 2 ^ (prefixWord ++ tailWord_367896).sum := by decide
  have hdescent : baseEnd_367896 < baseStart_367896 := by decide
  rcases family_descends (prefixWord ++ tailWord_367896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367903 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 1, 6]
def baseStart_367903 : Nat := 118140960795 + 367903 * 2 ^ 59
def prefixEnd_367903 : Nat := 4983230072969 + 3 ^ 40 * 367903 * 2
def baseEnd_367903 : Nat := 62970357743726437173517

theorem tailTrace_367903 : CollatzResearch.WordTrace tailWord_367903 prefixEnd_367903 62970357743726437173517 := by
  unfold tailWord_367903
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418524786157738675132363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8945683190771825783421575 13418524786157738675132363)
  ·
    refine ⟨20127787179236608012698545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13418524786157738675132363 20127787179236608012698545)
    ·
      refine ⟨15095840384427456009523909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20127787179236608012698545 15095840384427456009523909)
      ·
        refine ⟨2830470072080148001785733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15095840384427456009523909 2830470072080148001785733)
        ·
          refine ⟨530713138515027750334825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2830470072080148001785733 530713138515027750334825)
          ·
            refine ⟨398034853886270812751119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530713138515027750334825 398034853886270812751119)
            ·
              refine ⟨597052280829406219126679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398034853886270812751119 597052280829406219126679)
              ·
                refine ⟨895578421244109328690019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597052280829406219126679 895578421244109328690019)
                ·
                  refine ⟨1343367631866163993035029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895578421244109328690019 1343367631866163993035029)
                  ·
                    refine ⟨62970357743726437173517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1343367631866163993035029 62970357743726437173517)
                    ·
                      rfl

theorem cell23_367903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_367903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367903 prefixEnd_367903 := by exact prefixLift 367903
  have htrace : WordTrace (prefixWord ++ tailWord_367903) baseStart_367903 baseEnd_367903 := by
    simpa [prefixWord, tailWord_367903, baseEnd_367903] using wordTrace_append hprefix tailTrace_367903
  have hstable : (prefixWord ++ tailWord_367903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367903).length < 2 ^ (prefixWord ++ tailWord_367903).sum := by decide
  have hdescent : baseEnd_367903 < baseStart_367903 := by decide
  rcases family_descends (prefixWord ++ tailWord_367903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367933 : List Nat := [1, 4, 1, 5, 1, 2, 9]
def baseStart_367933 : Nat := 118140960795 + 367933 * 2 ^ 59
def prefixEnd_367933 : Nat := 4983230072969 + 3 ^ 40 * 367933 * 2
def baseEnd_367933 : Nat := 2332425650010051779573

theorem tailTrace_367933 : CollatzResearch.WordTrace tailWord_367933 prefixEnd_367933 2332425650010051779573 := by
  unfold tailWord_367933
  simp only [CollatzResearch.WordTrace]
  refine ⟨13419618976049053798724453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8946412650699369199149635 13419618976049053798724453)
  ·
    refine ⟨2516178558009197587260835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13419618976049053798724453 2516178558009197587260835)
    ·
      refine ⟨3774267837013796380891253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2516178558009197587260835 3774267837013796380891253)
      ·
        refine ⟨353837609720043410708555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3774267837013796380891253 353837609720043410708555)
        ·
          refine ⟨530756414580065116062833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353837609720043410708555 530756414580065116062833)
          ·
            refine ⟨398067310935048837047125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530756414580065116062833 398067310935048837047125)
            ·
              refine ⟨2332425650010051779573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 398067310935048837047125 2332425650010051779573)
              ·
                rfl

theorem cell23_367933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 9].length) (baseStart_367933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367933 prefixEnd_367933 := by exact prefixLift 367933
  have htrace : WordTrace (prefixWord ++ tailWord_367933) baseStart_367933 baseEnd_367933 := by
    simpa [prefixWord, tailWord_367933, baseEnd_367933] using wordTrace_append hprefix tailTrace_367933
  have hstable : (prefixWord ++ tailWord_367933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367933).length < 2 ^ (prefixWord ++ tailWord_367933).sum := by decide
  have hdescent : baseEnd_367933 < baseStart_367933 := by decide
  rcases family_descends (prefixWord ++ tailWord_367933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367939 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5]
def baseStart_367939 : Nat := 118140960795 + 367939 * 2 ^ 59
def prefixEnd_367939 : Nat := 4983230072969 + 3 ^ 40 * 367939 * 2
def baseEnd_367939 : Nat := 188929558534741170670385

theorem tailTrace_367939 : CollatzResearch.WordTrace tailWord_367939 prefixEnd_367939 188929558534741170670385 := by
  unfold tailWord_367939
  simp only [CollatzResearch.WordTrace]
  refine ⟨13419837814027316823442871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8946558542684877882295247 13419837814027316823442871)
  ·
    refine ⟨20129756721040975235164307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13419837814027316823442871 20129756721040975235164307)
    ·
      refine ⟨30194635081561462852746461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20129756721040975235164307 30194635081561462852746461)
      ·
        refine ⟨11322988155585548569779923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30194635081561462852746461 11322988155585548569779923)
        ·
          refine ⟨16984482233378322854669885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11322988155585548569779923 16984482233378322854669885)
          ·
            refine ⟨6369180837516871070501207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16984482233378322854669885 6369180837516871070501207)
            ·
              refine ⟨9553771256275306605751811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6369180837516871070501207 9553771256275306605751811)
              ·
                refine ⟨14330656884412959908627717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9553771256275306605751811 14330656884412959908627717)
                ·
                  refine ⟨2686998165827429982867697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14330656884412959908627717 2686998165827429982867697)
                  ·
                    refine ⟨2015248624370572487150773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2686998165827429982867697 2015248624370572487150773)
                    ·
                      refine ⟨188929558534741170670385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2015248624370572487150773 188929558534741170670385)
                      ·
                        rfl

theorem cell23_367939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_367939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367939 prefixEnd_367939 := by exact prefixLift 367939
  have htrace : WordTrace (prefixWord ++ tailWord_367939) baseStart_367939 baseEnd_367939 := by
    simpa [prefixWord, tailWord_367939, baseEnd_367939] using wordTrace_append hprefix tailTrace_367939
  have hstable : (prefixWord ++ tailWord_367939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367939).length < 2 ^ (prefixWord ++ tailWord_367939).sum := by decide
  have hdescent : baseEnd_367939 < baseStart_367939 := by decide
  rcases family_descends (prefixWord ++ tailWord_367939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367943 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_367943 : Nat := 118140960795 + 367943 * 2 ^ 59
def prefixEnd_367943 : Nat := 4983230072969 + 3 ^ 40 * 367943 * 2
def baseEnd_367943 : Nat := 188931612457359155020367

theorem tailTrace_367943 : CollatzResearch.WordTrace tailWord_367943 prefixEnd_367943 188931612457359155020367 := by
  unfold tailWord_367943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13419983706012825506588483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8946655804008550337725655 13419983706012825506588483)
  ·
    refine ⟨20129975559019238259882725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13419983706012825506588483 20129975559019238259882725)
    ·
      refine ⟨3774370417316107173728011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20129975559019238259882725 3774370417316107173728011)
      ·
        refine ⟨5661555625974160760592017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774370417316107173728011 5661555625974160760592017)
        ·
          refine ⟨4246166719480620570444013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5661555625974160760592017 4246166719480620570444013)
          ·
            refine ⟨1592312519805232713916505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4246166719480620570444013 1592312519805232713916505)
            ·
              refine ⟨1194234389853924535437379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592312519805232713916505 1194234389853924535437379)
              ·
                refine ⟨1791351584780886803156069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194234389853924535437379 1791351584780886803156069)
                ·
                  refine ⟨335878422146416275591763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791351584780886803156069 335878422146416275591763)
                  ·
                    refine ⟨503817633219624413387645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 335878422146416275591763 503817633219624413387645)
                    ·
                      refine ⟨188931612457359155020367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 503817633219624413387645 188931612457359155020367)
                      ·
                        rfl

theorem cell23_367943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_367943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367943 prefixEnd_367943 := by exact prefixLift 367943
  have htrace : WordTrace (prefixWord ++ tailWord_367943) baseStart_367943 baseEnd_367943 := by
    simpa [prefixWord, tailWord_367943, baseEnd_367943] using wordTrace_append hprefix tailTrace_367943
  have hstable : (prefixWord ++ tailWord_367943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367943).length < 2 ^ (prefixWord ++ tailWord_367943).sum := by decide
  have hdescent : baseEnd_367943 < baseStart_367943 := by decide
  rcases family_descends (prefixWord ++ tailWord_367943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367953 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 3, 3, 2]
def baseStart_367953 : Nat := 118140960795 + 367953 * 2 ^ 59
def prefixEnd_367953 : Nat := 4983230072969 + 3 ^ 40 * 367953 * 2
def baseEnd_367953 : Nat := 188936747263904115895321

theorem tailTrace_367953 : CollatzResearch.WordTrace tailWord_367953 prefixEnd_367953 188936747263904115895321 := by
  unfold tailWord_367953
  simp only [CollatzResearch.WordTrace]
  refine ⟨13420348435976597214452513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8946898957317731476301675 13420348435976597214452513)
  ·
    refine ⟨10065261326982447910839385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13420348435976597214452513 10065261326982447910839385)
    ·
      refine ⟨7548945995236835933129539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10065261326982447910839385 7548945995236835933129539)
      ·
        refine ⟨11323418992855253899694309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7548945995236835933129539 11323418992855253899694309)
        ·
          refine ⟨2123141061160360106192683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11323418992855253899694309 2123141061160360106192683)
          ·
            refine ⟨3184711591740540159289025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123141061160360106192683 3184711591740540159289025)
            ·
              refine ⟨2388533693805405119466769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184711591740540159289025 2388533693805405119466769)
              ·
                refine ⟨1791400270354053839600077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388533693805405119466769 1791400270354053839600077)
                ·
                  refine ⟨671775101382770189850029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1791400270354053839600077 671775101382770189850029)
                  ·
                    refine ⟨251915663018538821193761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671775101382770189850029 251915663018538821193761)
                    ·
                      refine ⟨188936747263904115895321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251915663018538821193761 188936747263904115895321)
                      ·
                        rfl

theorem cell23_367953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_367953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367953 prefixEnd_367953 := by exact prefixLift 367953
  have htrace : WordTrace (prefixWord ++ tailWord_367953) baseStart_367953 baseEnd_367953 := by
    simpa [prefixWord, tailWord_367953, baseEnd_367953] using wordTrace_append hprefix tailTrace_367953
  have hstable : (prefixWord ++ tailWord_367953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367953).length < 2 ^ (prefixWord ++ tailWord_367953).sum := by decide
  have hdescent : baseEnd_367953 < baseStart_367953 := by decide
  rcases family_descends (prefixWord ++ tailWord_367953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367970 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_367970 : Nat := 118140960795 + 367970 * 2 ^ 59
def prefixEnd_367970 : Nat := 4983230072969 + 3 ^ 40 * 367970 * 2
def baseEnd_367970 : Nat := 188945476435030549382743

theorem tailTrace_367970 : CollatzResearch.WordTrace tailWord_367970 prefixEnd_367970 188945476435030549382743 := by
  unfold tailWord_367970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355242119228752279455341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8947312317943339411880909 3355242119228752279455341)
  ·
    refine ⟨1258215794710782104795753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3355242119228752279455341 1258215794710782104795753)
    ·
      refine ⟨943661846033086578596815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1258215794710782104795753 943661846033086578596815)
      ·
        refine ⟨1415492769049629867895223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943661846033086578596815 1415492769049629867895223)
        ·
          refine ⟨2123239153574444801842835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1415492769049629867895223 2123239153574444801842835)
          ·
            refine ⟨3184858730361667202764253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123239153574444801842835 3184858730361667202764253)
            ·
              refine ⟨1194322023885625201036595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3184858730361667202764253 1194322023885625201036595)
              ·
                refine ⟨1791483035828437801554893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194322023885625201036595 1791483035828437801554893)
                ·
                  refine ⟨671806138435664175583085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1791483035828437801554893 671806138435664175583085)
                  ·
                    refine ⟨251927301913374065843657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 671806138435664175583085 251927301913374065843657)
                    ·
                      refine ⟨188945476435030549382743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251927301913374065843657 188945476435030549382743)
                      ·
                        rfl

theorem cell23_367970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_367970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367970 prefixEnd_367970 := by exact prefixLift 367970
  have htrace : WordTrace (prefixWord ++ tailWord_367970) baseStart_367970 baseEnd_367970 := by
    simpa [prefixWord, tailWord_367970, baseEnd_367970] using wordTrace_append hprefix tailTrace_367970
  have hstable : (prefixWord ++ tailWord_367970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367970).length < 2 ^ (prefixWord ++ tailWord_367970).sum := by decide
  have hdescent : baseEnd_367970 < baseStart_367970 := by decide
  rcases family_descends (prefixWord ++ tailWord_367970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367983 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 1, 4, 2]
def baseStart_367983 : Nat := 118140960795 + 367983 * 2 ^ 59
def prefixEnd_367983 : Nat := 4983230072969 + 3 ^ 40 * 367983 * 2
def baseEnd_367983 : Nat := 188952151683538998520183

theorem tailTrace_367983 : CollatzResearch.WordTrace tailWord_367983 prefixEnd_367983 188952151683538998520183 := by
  unfold tailWord_367983
  simp only [CollatzResearch.WordTrace]
  refine ⟨13421442625867912338044603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8947628417245274892029735 13421442625867912338044603)
  ·
    refine ⟨20132163938801868507066905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13421442625867912338044603 20132163938801868507066905)
    ·
      refine ⟨15099122954101401380300179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20132163938801868507066905 15099122954101401380300179)
      ·
        refine ⟨22648684431152102070450269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15099122954101401380300179 22648684431152102070450269)
        ·
          refine ⟨8493256661682038276418851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22648684431152102070450269 8493256661682038276418851)
          ·
            refine ⟨12739884992523057414628277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493256661682038276418851 12739884992523057414628277)
            ·
              refine ⟨1194364218049036632621401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12739884992523057414628277 1194364218049036632621401)
              ·
                refine ⟨895773163536777474466051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194364218049036632621401 895773163536777474466051)
                ·
                  refine ⟨1343659745305166211699077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895773163536777474466051 1343659745305166211699077)
                  ·
                    refine ⟨251936202244718664693577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1343659745305166211699077 251936202244718664693577)
                    ·
                      refine ⟨188952151683538998520183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 251936202244718664693577 188952151683538998520183)
                      ·
                        rfl

theorem cell23_367983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 4, 2].length) (baseStart_367983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367983 prefixEnd_367983 := by exact prefixLift 367983
  have htrace : WordTrace (prefixWord ++ tailWord_367983) baseStart_367983 baseEnd_367983 := by
    simpa [prefixWord, tailWord_367983, baseEnd_367983] using wordTrace_append hprefix tailTrace_367983
  have hstable : (prefixWord ++ tailWord_367983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367983).length < 2 ^ (prefixWord ++ tailWord_367983).sum := by decide
  have hdescent : baseEnd_367983 < baseStart_367983 := by decide
  rcases family_descends (prefixWord ++ tailWord_367983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367986 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_367986 : Nat := 118140960795 + 367986 * 2 ^ 59
def prefixEnd_367986 : Nat := 4983230072969 + 3 ^ 40 * 367986 * 2
def baseEnd_367986 : Nat := 188953692125502486782669

theorem tailTrace_367986 : CollatzResearch.WordTrace tailWord_367986 prefixEnd_367986 188953692125502486782669 := by
  unfold tailWord_367986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355388011214260962600953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8947701363238029233602541 3355388011214260962600953)
  ·
    refine ⟨2516541008410695721950715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3355388011214260962600953 2516541008410695721950715)
    ·
      refine ⟨3774811512616043582926073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2516541008410695721950715 3774811512616043582926073)
      ·
        refine ⟨2831108634462032687194555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3774811512616043582926073 2831108634462032687194555)
        ·
          refine ⟨4246662951693049030791833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831108634462032687194555 4246662951693049030791833)
          ·
            refine ⟨3184997213769786773093875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4246662951693049030791833 3184997213769786773093875)
            ·
              refine ⟨4777495820654680159640813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184997213769786773093875 4777495820654680159640813)
              ·
                refine ⟨1791560932745505059865305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4777495820654680159640813 1791560932745505059865305)
                ·
                  refine ⟨1343670699559128794898979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1791560932745505059865305 1343670699559128794898979)
                  ·
                    refine ⟨2015506049338693192348469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1343670699559128794898979 2015506049338693192348469)
                    ·
                      refine ⟨188953692125502486782669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2015506049338693192348469 188953692125502486782669)
                      ·
                        rfl

theorem cell23_367986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_367986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367986 prefixEnd_367986 := by exact prefixLift 367986
  have htrace : WordTrace (prefixWord ++ tailWord_367986) baseStart_367986 baseEnd_367986 := by
    simpa [prefixWord, tailWord_367986, baseEnd_367986] using wordTrace_append hprefix tailTrace_367986
  have hstable : (prefixWord ++ tailWord_367986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367986).length < 2 ^ (prefixWord ++ tailWord_367986).sum := by decide
  have hdescent : baseEnd_367986 < baseStart_367986 := by decide
  rcases family_descends (prefixWord ++ tailWord_367986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367996 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_367996 : Nat := 118140960795 + 367996 * 2 ^ 59
def prefixEnd_367996 : Nat := 4983230072969 + 3 ^ 40 * 367996 * 2
def baseEnd_367996 : Nat := 188958826932047447657623

theorem tailTrace_367996 : CollatzResearch.WordTrace tailWord_367996 prefixEnd_367996 188958826932047447657623 := by
  unfold tailWord_367996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6710958387410407779133921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8947944516547210372178561 6710958387410407779133921)
  ·
    refine ⟨5033218790557805834350441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6710958387410407779133921 5033218790557805834350441)
    ·
      refine ⟨3774914092918354375762831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5033218790557805834350441 3774914092918354375762831)
      ·
        refine ⟨5662371139377531563644247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774914092918354375762831 5662371139377531563644247)
        ·
          refine ⟨8493556709066297345466371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662371139377531563644247 8493556709066297345466371)
          ·
            refine ⟨12740335063599446018199557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493556709066297345466371 12740335063599446018199557)
            ·
              refine ⟨2388812824424896128412417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12740335063599446018199557 2388812824424896128412417)
              ·
                refine ⟨1791609618318672096309313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388812824424896128412417 1791609618318672096309313)
                ·
                  refine ⟨1343707213739004072231985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1791609618318672096309313 1343707213739004072231985)
                  ·
                    refine ⟨1007780410304253054173989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343707213739004072231985 1007780410304253054173989)
                    ·
                      refine ⟨188958826932047447657623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1007780410304253054173989 188958826932047447657623)
                      ·
                        rfl

theorem cell23_367996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_367996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_367996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_367996 prefixEnd_367996 := by exact prefixLift 367996
  have htrace : WordTrace (prefixWord ++ tailWord_367996) baseStart_367996 baseEnd_367996 := by
    simpa [prefixWord, tailWord_367996, baseEnd_367996] using wordTrace_append hprefix tailTrace_367996
  have hstable : (prefixWord ++ tailWord_367996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367996).length < 2 ^ (prefixWord ++ tailWord_367996).sum := by decide
  have hdescent : baseEnd_367996 < baseStart_367996 := by decide
  rcases family_descends (prefixWord ++ tailWord_367996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368110 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_368110 : Nat := 118140960795 + 368110 * 2 ^ 59
def prefixEnd_368110 : Nat := 4983230072969 + 3 ^ 40 * 368110 * 2
def baseEnd_368110 : Nat := 189017363726660001632099

theorem tailTrace_368110 : CollatzResearch.WordTrace tailWord_368110 prefixEnd_368110 189017363726660001632099 := by
  unfold tailWord_368110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678259337050976628489723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8950716464271875351945189 1678259337050976628489723)
  ·
    refine ⟨2517389005576464942734585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1678259337050976628489723 2517389005576464942734585)
    ·
      refine ⟨1888041754182348707050939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2517389005576464942734585 1888041754182348707050939)
      ·
        refine ⟨2832062631273523060576409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888041754182348707050939 2832062631273523060576409)
        ·
          refine ⟨2124046973455142295432307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2832062631273523060576409 2124046973455142295432307)
          ·
            refine ⟨3186070460182713443148461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124046973455142295432307 3186070460182713443148461)
            ·
              refine ⟨1194776422568517541180673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3186070460182713443148461 1194776422568517541180673)
              ·
                refine ⟨896082316926388155885505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194776422568517541180673 896082316926388155885505)
                ·
                  refine ⟨672061737694791116914129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896082316926388155885505 672061737694791116914129)
                  ·
                    refine ⟨504046303271093337685597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 672061737694791116914129 504046303271093337685597)
                    ·
                      refine ⟨189017363726660001632099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 504046303271093337685597 189017363726660001632099)
                      ·
                        rfl

theorem cell23_368110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_368110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368110 prefixEnd_368110 := by exact prefixLift 368110
  have htrace : WordTrace (prefixWord ++ tailWord_368110) baseStart_368110 baseEnd_368110 := by
    simpa [prefixWord, tailWord_368110, baseEnd_368110] using wordTrace_append hprefix tailTrace_368110
  have hstable : (prefixWord ++ tailWord_368110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368110).length < 2 ^ (prefixWord ++ tailWord_368110).sum := by decide
  have hdescent : baseEnd_368110 < baseStart_368110 := by decide
  rcases family_descends (prefixWord ++ tailWord_368110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368117 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_368117 : Nat := 118140960795 + 368117 * 2 ^ 59
def prefixEnd_368117 : Nat := 4983230072969 + 3 ^ 40 * 368117 * 2
def baseEnd_368117 : Nat := 63006986030413824748189

theorem tailTrace_368117 : CollatzResearch.WordTrace tailWord_368117 prefixEnd_368117 63006986030413824748189 := by
  unfold tailWord_368117
  simp only [CollatzResearch.WordTrace]
  refine ⟨13426330007382453223422605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8950886671588302148948403 13426330007382453223422605)
  ·
    refine ⟨5034873752768419958783477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13426330007382453223422605 5034873752768419958783477)
    ·
      refine ⟨472019414322039371135951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5034873752768419958783477 472019414322039371135951)
      ·
        refine ⟨708029121483059056703927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472019414322039371135951 708029121483059056703927)
        ·
          refine ⟨1062043682224588585055891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708029121483059056703927 1062043682224588585055891)
          ·
            refine ⟨1593065523336882877583837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062043682224588585055891 1593065523336882877583837)
            ·
              refine ⟨597399571251331079093939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593065523336882877583837 597399571251331079093939)
              ·
                refine ⟨896099356876996618640909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597399571251331079093939 896099356876996618640909)
                ·
                  refine ⟨336037258828873731990341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896099356876996618640909 336037258828873731990341)
                  ·
                    refine ⟨63006986030413824748189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336037258828873731990341 63006986030413824748189)
                    ·
                      rfl

theorem cell23_368117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_368117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368117 prefixEnd_368117 := by exact prefixLift 368117
  have htrace : WordTrace (prefixWord ++ tailWord_368117) baseStart_368117 baseEnd_368117 := by
    simpa [prefixWord, tailWord_368117, baseEnd_368117] using wordTrace_append hprefix tailTrace_368117
  have hstable : (prefixWord ++ tailWord_368117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368117).length < 2 ^ (prefixWord ++ tailWord_368117).sum := by decide
  have hdescent : baseEnd_368117 < baseStart_368117 := by decide
  rcases family_descends (prefixWord ++ tailWord_368117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368168 : List Nat := [2, 1, 5, 2, 3, 1, 2, 2, 1, 4]
def baseStart_368168 : Nat := 118140960795 + 368168 * 2 ^ 59
def prefixEnd_368168 : Nat := 4983230072969 + 3 ^ 40 * 368168 * 2
def baseEnd_368168 : Nat := 63015715201540258235611

theorem tailTrace_368168 : CollatzResearch.WordTrace tailWord_368168 prefixEnd_368168 63015715201540258235611 := by
  unfold tailWord_368168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714095065098844466764579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8952126753465125955686105 6714095065098844466764579)
  ·
    refine ⟨10071142597648266700146869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6714095065098844466764579 10071142597648266700146869)
    ·
      refine ⟨944169618529525003138769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10071142597648266700146869 944169618529525003138769)
      ·
        refine ⟨708127213897143752354077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 944169618529525003138769 708127213897143752354077)
        ·
          refine ⟨265547705211428907132779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 708127213897143752354077 265547705211428907132779)
          ·
            refine ⟨398321557817143360699169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265547705211428907132779 398321557817143360699169)
            ·
              refine ⟨298741168362857520524377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398321557817143360699169 298741168362857520524377)
              ·
                refine ⟨224055876272143140393283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298741168362857520524377 224055876272143140393283)
                ·
                  refine ⟨336083814408214710589925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224055876272143140393283 336083814408214710589925)
                  ·
                    refine ⟨63015715201540258235611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336083814408214710589925 63015715201540258235611)
                    ·
                      rfl

theorem cell23_368168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_368168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368168 prefixEnd_368168 := by exact prefixLift 368168
  have htrace : WordTrace (prefixWord ++ tailWord_368168) baseStart_368168 baseEnd_368168 := by
    simpa [prefixWord, tailWord_368168, baseEnd_368168] using wordTrace_append hprefix tailTrace_368168
  have hstable : (prefixWord ++ tailWord_368168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368168).length < 2 ^ (prefixWord ++ tailWord_368168).sum := by decide
  have hdescent : baseEnd_368168 < baseStart_368168 := by decide
  rcases family_descends (prefixWord ++ tailWord_368168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368197 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 3, 2, 2]
def baseStart_368197 : Nat := 118140960795 + 368197 * 2 ^ 59
def prefixEnd_368197 : Nat := 4983230072969 + 3 ^ 40 * 368197 * 2
def baseEnd_368197 : Nat := 189062036543601161244199

theorem tailTrace_368197 : CollatzResearch.WordTrace tailWord_368197 prefixEnd_368197 189062036543601161244199 := by
  unfold tailWord_368197
  simp only [CollatzResearch.WordTrace]
  refine ⟨13429247847092626886334845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8952831898061751257556563 13429247847092626886334845)
  ·
    refine ⟨5035967942659735082375567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13429247847092626886334845 5035967942659735082375567)
    ·
      refine ⟨7553951913989602623563351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5035967942659735082375567 7553951913989602623563351)
      ·
        refine ⟨11330927870984403935345027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7553951913989602623563351 11330927870984403935345027)
        ·
          refine ⟨16996391806476605903017541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11330927870984403935345027 16996391806476605903017541)
          ·
            refine ⟨3186823463714363606815789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16996391806476605903017541 3186823463714363606815789)
            ·
              refine ⟨1195058798892886352555921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3186823463714363606815789 1195058798892886352555921)
              ·
                refine ⟨896294099169664764416941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195058798892886352555921 896294099169664764416941)
                ·
                  refine ⟨336110287188624286656353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896294099169664764416941 336110287188624286656353)
                  ·
                    refine ⟨252082715391468214992265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 336110287188624286656353 252082715391468214992265)
                    ·
                      refine ⟨189062036543601161244199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 252082715391468214992265 189062036543601161244199)
                      ·
                        rfl

theorem cell23_368197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_368197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368197 prefixEnd_368197 := by exact prefixLift 368197
  have htrace : WordTrace (prefixWord ++ tailWord_368197) baseStart_368197 baseEnd_368197 := by
    simpa [prefixWord, tailWord_368197, baseEnd_368197] using wordTrace_append hprefix tailTrace_368197
  have hstable : (prefixWord ++ tailWord_368197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368197).length < 2 ^ (prefixWord ++ tailWord_368197).sum := by decide
  have hdescent : baseEnd_368197 < baseStart_368197 := by decide
  rcases family_descends (prefixWord ++ tailWord_368197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368210 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_368210 : Nat := 118140960795 + 368210 * 2 ^ 59
def prefixEnd_368210 : Nat := 4983230072969 + 3 ^ 40 * 368210 * 2
def baseEnd_368210 : Nat := 189068711792109610381639

theorem tailTrace_368210 : CollatzResearch.WordTrace tailWord_368210 prefixEnd_368210 189068711792109610381639 := by
  unfold tailWord_368210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357430499011382526639521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8953147997363686737705389 3357430499011382526639521)
  ·
    refine ⟨2518072874258536894979641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3357430499011382526639521 2518072874258536894979641)
    ·
      refine ⟨1888554655693902671234731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2518072874258536894979641 1888554655693902671234731)
      ·
        refine ⟨2832831983540854006852097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888554655693902671234731 2832831983540854006852097)
        ·
          refine ⟨2124623987655640505139073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2832831983540854006852097 2124623987655640505139073)
          ·
            refine ⟨1593467990741730378854305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124623987655640505139073 1593467990741730378854305)
            ·
              refine ⟨1195100993056297784140729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1593467990741730378854305 1195100993056297784140729)
              ·
                refine ⟨896325744792223338105547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195100993056297784140729 896325744792223338105547)
                ·
                  refine ⟨1344488617188335007158321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896325744792223338105547 1344488617188335007158321)
                  ·
                    refine ⟨1008366462891251255368741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1344488617188335007158321 1008366462891251255368741)
                    ·
                      refine ⟨189068711792109610381639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1008366462891251255368741 189068711792109610381639)
                      ·
                        rfl

theorem cell23_368210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_368210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368210 prefixEnd_368210 := by exact prefixLift 368210
  have htrace : WordTrace (prefixWord ++ tailWord_368210) baseStart_368210 baseEnd_368210 := by
    simpa [prefixWord, tailWord_368210, baseEnd_368210] using wordTrace_append hprefix tailTrace_368210
  have hstable : (prefixWord ++ tailWord_368210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368210).length < 2 ^ (prefixWord ++ tailWord_368210).sum := by decide
  have hdescent : baseEnd_368210 < baseStart_368210 := by decide
  rcases family_descends (prefixWord ++ tailWord_368210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368374 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_368374 : Nat := 118140960795 + 368374 * 2 ^ 59
def prefixEnd_368374 : Nat := 4983230072969 + 3 ^ 40 * 368374 * 2
def baseEnd_368374 : Nat := 63050974206482322910295

theorem tailTrace_368374 : CollatzResearch.WordTrace tailWord_368374 prefixEnd_368374 63050974206482322910295 := by
  unfold tailWord_368374
  simp only [CollatzResearch.WordTrace]
  refine ⟨839731472965711632220511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8957135711634257410352117 839731472965711632220511)
  ·
    refine ⟨1259597209448567448330767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839731472965711632220511 1259597209448567448330767)
    ·
      refine ⟨1889395814172851172496151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1259597209448567448330767 1889395814172851172496151)
      ·
        refine ⟨2834093721259276758744227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889395814172851172496151 2834093721259276758744227)
        ·
          refine ⟨4251140581888915138116341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834093721259276758744227 4251140581888915138116341)
          ·
            refine ⟨398544429552085794198407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4251140581888915138116341 398544429552085794198407)
            ·
              refine ⟨597816644328128691297611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398544429552085794198407 597816644328128691297611)
              ·
                refine ⟨896724966492193036946417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597816644328128691297611 896724966492193036946417)
                ·
                  refine ⟨672543724869144777709813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896724966492193036946417 672543724869144777709813)
                  ·
                    refine ⟨63050974206482322910295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 672543724869144777709813 63050974206482322910295)
                    ·
                      rfl

theorem cell23_368374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_368374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368374 prefixEnd_368374 := by exact prefixLift 368374
  have htrace : WordTrace (prefixWord ++ tailWord_368374) baseStart_368374 baseEnd_368374 := by
    simpa [prefixWord, tailWord_368374, baseEnd_368374] using wordTrace_append hprefix tailTrace_368374
  have hstable : (prefixWord ++ tailWord_368374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368374).length < 2 ^ (prefixWord ++ tailWord_368374).sum := by decide
  have hdescent : baseEnd_368374 < baseStart_368374 := by decide
  rcases family_descends (prefixWord ++ tailWord_368374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368438 : List Nat := [5, 1, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_368438 : Nat := 118140960795 + 368438 * 2 ^ 59
def prefixEnd_368438 : Nat := 4983230072969 + 3 ^ 40 * 368438 * 2
def baseEnd_368438 : Nat := 63061928460444906110197

theorem tailTrace_368438 : CollatzResearch.WordTrace tailWord_368438 prefixEnd_368438 63061928460444906110197 := by
  unfold tailWord_368438
  simp only [CollatzResearch.WordTrace]
  refine ⟨839877364951220315366123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8958691892813016697238645 839877364951220315366123)
  ·
    refine ⟨1259816047426830473049185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839877364951220315366123 1259816047426830473049185)
    ·
      refine ⟨944862035570122854786889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1259816047426830473049185 944862035570122854786889)
      ·
        refine ⟨708646526677592141090167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 944862035570122854786889 708646526677592141090167)
        ·
          refine ⟨1062969790016388211635251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708646526677592141090167 1062969790016388211635251)
          ·
            refine ⟨1594454685024582317452877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062969790016388211635251 1594454685024582317452877)
            ·
              refine ⟨597920506884218369044829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1594454685024582317452877 597920506884218369044829)
              ·
                refine ⟨224220190081581888391811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 597920506884218369044829 224220190081581888391811)
                ·
                  refine ⟨336330285122372832587717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224220190081581888391811 336330285122372832587717)
                  ·
                    refine ⟨63061928460444906110197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336330285122372832587717 63061928460444906110197)
                    ·
                      rfl

theorem cell23_368438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_368438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368438 prefixEnd_368438 := by exact prefixLift 368438
  have htrace : WordTrace (prefixWord ++ tailWord_368438) baseStart_368438 baseEnd_368438 := by
    simpa [prefixWord, tailWord_368438, baseEnd_368438] using wordTrace_append hprefix tailTrace_368438
  have hstable : (prefixWord ++ tailWord_368438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368438).length < 2 ^ (prefixWord ++ tailWord_368438).sum := by decide
  have hdescent : baseEnd_368438 < baseStart_368438 := by decide
  rcases family_descends (prefixWord ++ tailWord_368438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368484 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_368484 : Nat := 118140960795 + 368484 * 2 ^ 59
def prefixEnd_368484 : Nat := 4983230072969 + 3 ^ 40 * 368484 * 2
def baseEnd_368484 : Nat := 189209405491441538355379

theorem tailTrace_368484 : CollatzResearch.WordTrace tailWord_368484 prefixEnd_368484 189209405491441538355379 := by
  unfold tailWord_368484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719857798526437451016253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8959810398035249934688337 6719857798526437451016253)
  ·
    refine ⟨2519946674447414044131095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6719857798526437451016253 2519946674447414044131095)
    ·
      refine ⟨3779920011671121066196643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519946674447414044131095 3779920011671121066196643)
      ·
        refine ⟨5669880017506681599294965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779920011671121066196643 5669880017506681599294965)
        ·
          refine ⟨531551251641251399933903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5669880017506681599294965 531551251641251399933903)
          ·
            refine ⟨797326877461877099900855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531551251641251399933903 797326877461877099900855)
            ·
              refine ⟨1195990316192815649851283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797326877461877099900855 1195990316192815649851283)
              ·
                refine ⟨1793985474289223474776925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195990316192815649851283 1793985474289223474776925)
                ·
                  refine ⟨672744552858458803041347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1793985474289223474776925 672744552858458803041347)
                  ·
                    refine ⟨1009116829287688204562021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 672744552858458803041347 1009116829287688204562021)
                    ·
                      refine ⟨189209405491441538355379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1009116829287688204562021 189209405491441538355379)
                      ·
                        rfl

theorem cell23_368484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_368484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368484 prefixEnd_368484 := by exact prefixLift 368484
  have htrace : WordTrace (prefixWord ++ tailWord_368484) baseStart_368484 baseEnd_368484 := by
    simpa [prefixWord, tailWord_368484, baseEnd_368484] using wordTrace_append hprefix tailTrace_368484
  have hstable : (prefixWord ++ tailWord_368484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368484).length < 2 ^ (prefixWord ++ tailWord_368484).sum := by decide
  have hdescent : baseEnd_368484 < baseStart_368484 := by decide
  rcases family_descends (prefixWord ++ tailWord_368484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368494 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_368494 : Nat := 118140960795 + 368494 * 2 ^ 59
def prefixEnd_368494 : Nat := 4983230072969 + 3 ^ 40 * 368494 * 2
def baseEnd_368494 : Nat := 63071513432662166410111

theorem tailTrace_368494 : CollatzResearch.WordTrace tailWord_368494 prefixEnd_368494 63071513432662166410111 := by
  unfold tailWord_368494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1680010040877080826237067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8960053551344431073264357 1680010040877080826237067)
  ·
    refine ⟨2520015061315621239355601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1680010040877080826237067 2520015061315621239355601)
    ·
      refine ⟨1890011295986715929516701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2520015061315621239355601 1890011295986715929516701)
      ·
        refine ⟨708754235995018473568763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1890011295986715929516701 708754235995018473568763)
        ·
          refine ⟨1063131353992527710353145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708754235995018473568763 1063131353992527710353145)
          ·
            refine ⟨797348515494395782764859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1063131353992527710353145 797348515494395782764859)
            ·
              refine ⟨1196022773241593674147289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797348515494395782764859 1196022773241593674147289)
              ·
                refine ⟨897017079931195255610467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196022773241593674147289 897017079931195255610467)
                ·
                  refine ⟨1345525619896792883415701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897017079931195255610467 1345525619896792883415701)
                  ·
                    refine ⟨63071513432662166410111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1345525619896792883415701 63071513432662166410111)
                    ·
                      rfl

theorem cell23_368494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_368494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368494 prefixEnd_368494 := by exact prefixLift 368494
  have htrace : WordTrace (prefixWord ++ tailWord_368494) baseStart_368494 baseEnd_368494 := by
    simpa [prefixWord, tailWord_368494, baseEnd_368494] using wordTrace_append hprefix tailTrace_368494
  have hstable : (prefixWord ++ tailWord_368494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368494).length < 2 ^ (prefixWord ++ tailWord_368494).sum := by decide
  have hdescent : baseEnd_368494 < baseStart_368494 := by decide
  rcases family_descends (prefixWord ++ tailWord_368494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368497 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_368497 : Nat := 118140960795 + 368497 * 2 ^ 59
def prefixEnd_368497 : Nat := 4983230072969 + 3 ^ 40 * 368497 * 2
def baseEnd_368497 : Nat := 189216080739949987492819

theorem tailTrace_368497 : CollatzResearch.WordTrace tailWord_368497 prefixEnd_368497 189216080739949987492819 := by
  unfold tailWord_368497
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440189746005778122255745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8960126497337185414837163 13440189746005778122255745)
  ·
    refine ⟨10080142309504333591691809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13440189746005778122255745 10080142309504333591691809)
    ·
      refine ⟨7560106732128250193768857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10080142309504333591691809 7560106732128250193768857)
      ·
        refine ⟨5670080049096187645326643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7560106732128250193768857 5670080049096187645326643)
        ·
          refine ⟨8505120073644281467989965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5670080049096187645326643 8505120073644281467989965)
          ·
            refine ⟨3189420027616605550496237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8505120073644281467989965 3189420027616605550496237)
            ·
              refine ⟨1196032510356227081436089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3189420027616605550496237 1196032510356227081436089)
              ·
                refine ⟨897024382767170311077067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196032510356227081436089 897024382767170311077067)
                ·
                  refine ⟨1345536574150755466615601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 897024382767170311077067 1345536574150755466615601)
                  ·
                    refine ⟨1009152430613066599961701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345536574150755466615601 1009152430613066599961701)
                    ·
                      refine ⟨189216080739949987492819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1009152430613066599961701 189216080739949987492819)
                      ·
                        rfl

theorem cell23_368497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_368497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368497 prefixEnd_368497 := by exact prefixLift 368497
  have htrace : WordTrace (prefixWord ++ tailWord_368497) baseStart_368497 baseEnd_368497 := by
    simpa [prefixWord, tailWord_368497, baseEnd_368497] using wordTrace_append hprefix tailTrace_368497
  have hstable : (prefixWord ++ tailWord_368497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368497).length < 2 ^ (prefixWord ++ tailWord_368497).sum := by decide
  have hdescent : baseEnd_368497 < baseStart_368497 := by decide
  rcases family_descends (prefixWord ++ tailWord_368497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368501 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_368501 : Nat := 118140960795 + 368501 * 2 ^ 59
def prefixEnd_368501 : Nat := 4983230072969 + 3 ^ 40 * 368501 * 2
def baseEnd_368501 : Nat := 189218134662567971842801

theorem tailTrace_368501 : CollatzResearch.WordTrace tailWord_368501 prefixEnd_368501 189218134662567971842801 := by
  unfold tailWord_368501
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440335637991286805401357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8960223758660857870267571 13440335637991286805401357)
  ·
    refine ⟨5040125864246732552025509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13440335637991286805401357 5040125864246732552025509)
    ·
      refine ⟨945023599546262353504783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5040125864246732552025509 945023599546262353504783)
      ·
        refine ⟨1417535399319393530257175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945023599546262353504783 1417535399319393530257175)
        ·
          refine ⟨2126303098979090295385763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417535399319393530257175 2126303098979090295385763)
          ·
            refine ⟨3189454648468635443078645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126303098979090295385763 3189454648468635443078645)
            ·
              refine ⟨299011373293934572788623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3189454648468635443078645 299011373293934572788623)
              ·
                refine ⟨448517059940901859182935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299011373293934572788623 448517059940901859182935)
                ·
                  refine ⟨672775589911352788774403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448517059940901859182935 672775589911352788774403)
                  ·
                    refine ⟨1009163384867029183161605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 672775589911352788774403 1009163384867029183161605)
                    ·
                      refine ⟨189218134662567971842801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1009163384867029183161605 189218134662567971842801)
                      ·
                        rfl

theorem cell23_368501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_368501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368501 prefixEnd_368501 := by exact prefixLift 368501
  have htrace : WordTrace (prefixWord ++ tailWord_368501) baseStart_368501 baseEnd_368501 := by
    simpa [prefixWord, tailWord_368501, baseEnd_368501] using wordTrace_append hprefix tailTrace_368501
  have hstable : (prefixWord ++ tailWord_368501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368501).length < 2 ^ (prefixWord ++ tailWord_368501).sum := by decide
  have hdescent : baseEnd_368501 < baseStart_368501 := by decide
  rcases family_descends (prefixWord ++ tailWord_368501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368517 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_368517 : Nat := 118140960795 + 368517 * 2 ^ 59
def prefixEnd_368517 : Nat := 4983230072969 + 3 ^ 40 * 368517 * 2
def baseEnd_368517 : Nat := 189226350353039909242727

theorem tailTrace_368517 : CollatzResearch.WordTrace tailWord_368517 prefixEnd_368517 189226350353039909242727 := by
  unfold tailWord_368517
  simp only [CollatzResearch.WordTrace]
  refine ⟨13440919205933321537983805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8960612803955547691989203 13440919205933321537983805)
  ·
    refine ⟨5040344702224995576743927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13440919205933321537983805 5040344702224995576743927)
    ·
      refine ⟨7560517053337493365115891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040344702224995576743927 7560517053337493365115891)
      ·
        refine ⟨11340775580006240047673837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7560517053337493365115891 11340775580006240047673837)
        ·
          refine ⟨4252790842502340017877689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11340775580006240047673837 4252790842502340017877689)
          ·
            refine ⟨3189593131876755013408267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4252790842502340017877689 3189593131876755013408267)
            ·
              refine ⟨4784389697815132520112401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3189593131876755013408267 4784389697815132520112401)
              ·
                refine ⟨3588292273361349390084301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4784389697815132520112401 3588292273361349390084301)
                ·
                  refine ⟨1345609602510506021281613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3588292273361349390084301 1345609602510506021281613)
                  ·
                    refine ⟨504603600941439757980605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1345609602510506021281613 504603600941439757980605)
                    ·
                      refine ⟨189226350353039909242727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 504603600941439757980605 189226350353039909242727)
                      ·
                        rfl

theorem cell23_368517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_368517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368517 prefixEnd_368517 := by exact prefixLift 368517
  have htrace : WordTrace (prefixWord ++ tailWord_368517) baseStart_368517 baseEnd_368517 := by
    simpa [prefixWord, tailWord_368517, baseEnd_368517] using wordTrace_append hprefix tailTrace_368517
  have hstable : (prefixWord ++ tailWord_368517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368517).length < 2 ^ (prefixWord ++ tailWord_368517).sum := by decide
  have hdescent : baseEnd_368517 < baseStart_368517 := by decide
  rcases family_descends (prefixWord ++ tailWord_368517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368552 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_368552 : Nat := 118140960795 + 368552 * 2 ^ 59
def prefixEnd_368552 : Nat := 4983230072969 + 3 ^ 40 * 368552 * 2
def baseEnd_368552 : Nat := 189244322175947272305067

theorem tailTrace_368552 : CollatzResearch.WordTrace tailWord_368552 prefixEnd_368552 189244322175947272305067 := by
  unfold tailWord_368552
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721097880403261257753955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8961463840537681677005273 6721097880403261257753955)
  ·
    refine ⟨10081646820604891886630933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721097880403261257753955 10081646820604891886630933)
    ·
      refine ⟨472577194715854307185825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10081646820604891886630933 472577194715854307185825)
      ·
        refine ⟨354432896036890730389369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472577194715854307185825 354432896036890730389369)
        ·
          refine ⟨265824672027668047792027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354432896036890730389369 265824672027668047792027)
          ·
            refine ⟨398737008041502071688041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265824672027668047792027 398737008041502071688041)
            ·
              refine ⟨299052756031126553766031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398737008041502071688041 299052756031126553766031)
              ·
                refine ⟨448579134046689830649047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299052756031126553766031 448579134046689830649047)
                ·
                  refine ⟨672868701070034745973571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448579134046689830649047 672868701070034745973571)
                  ·
                    refine ⟨1009303051605052118960357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 672868701070034745973571 1009303051605052118960357)
                    ·
                      refine ⟨189244322175947272305067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1009303051605052118960357 189244322175947272305067)
                      ·
                        rfl

theorem cell23_368552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_368552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368552 prefixEnd_368552 := by exact prefixLift 368552
  have htrace : WordTrace (prefixWord ++ tailWord_368552) baseStart_368552 baseEnd_368552 := by
    simpa [prefixWord, tailWord_368552, baseEnd_368552] using wordTrace_append hprefix tailTrace_368552
  have hstable : (prefixWord ++ tailWord_368552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368552).length < 2 ^ (prefixWord ++ tailWord_368552).sum := by decide
  have hdescent : baseEnd_368552 < baseStart_368552 := by decide
  rcases family_descends (prefixWord ++ tailWord_368552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368587 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4]
def baseStart_368587 : Nat := 118140960795 + 368587 * 2 ^ 59
def prefixEnd_368587 : Nat := 4983230072969 + 3 ^ 40 * 368587 * 2
def baseEnd_368587 : Nat := 189262293998854635367405

theorem tailTrace_368587 : CollatzResearch.WordTrace tailWord_368587 prefixEnd_368587 189262293998854635367405 := by
  unfold tailWord_368587
  simp only [CollatzResearch.WordTrace]
  refine ⟨13443472315679723493032015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8962314877119815662021343 13443472315679723493032015)
  ·
    refine ⟨20165208473519585239548023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13443472315679723493032015 20165208473519585239548023)
    ·
      refine ⟨30247812710279377859322035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20165208473519585239548023 30247812710279377859322035)
      ·
        refine ⟨45371719065419066788983053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30247812710279377859322035 45371719065419066788983053)
        ·
          refine ⟨17014394649532150045868645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45371719065419066788983053 17014394649532150045868645)
          ·
            refine ⟨3190198996787278133600371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17014394649532150045868645 3190198996787278133600371)
            ·
              refine ⟨4785298495180917200400557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190198996787278133600371 4785298495180917200400557)
              ·
                refine ⟨1794486935692843950150209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4785298495180917200400557 1794486935692843950150209)
                ·
                  refine ⟨1345865201769632962612657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1794486935692843950150209 1345865201769632962612657)
                  ·
                    refine ⟨1009398901327224721959493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345865201769632962612657 1009398901327224721959493)
                    ·
                      refine ⟨189262293998854635367405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1009398901327224721959493 189262293998854635367405)
                      ·
                        rfl

theorem cell23_368587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_368587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368587 prefixEnd_368587 := by exact prefixLift 368587
  have htrace : WordTrace (prefixWord ++ tailWord_368587) baseStart_368587 baseEnd_368587 := by
    simpa [prefixWord, tailWord_368587, baseEnd_368587] using wordTrace_append hprefix tailTrace_368587
  have hstable : (prefixWord ++ tailWord_368587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368587).length < 2 ^ (prefixWord ++ tailWord_368587).sum := by decide
  have hdescent : baseEnd_368587 < baseStart_368587 := by decide
  rcases family_descends (prefixWord ++ tailWord_368587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368637 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_368637 : Nat := 118140960795 + 368637 * 2 ^ 59
def prefixEnd_368637 : Nat := 4983230072969 + 3 ^ 40 * 368637 * 2
def baseEnd_368637 : Nat := 189287968031579439742175

theorem tailTrace_368637 : CollatzResearch.WordTrace tailWord_368637 prefixEnd_368637 189287968031579439742175 := by
  unfold tailWord_368637
  simp only [CollatzResearch.WordTrace]
  refine ⟨13445295965498582032352165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8963530643665721354901443 13445295965498582032352165)
  ·
    refine ⟨2520992993530984131066031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13445295965498582032352165 2520992993530984131066031)
    ·
      refine ⟨3781489490296476196599047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2520992993530984131066031 3781489490296476196599047)
      ·
        refine ⟨5672234235444714294898571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781489490296476196599047 5672234235444714294898571)
        ·
          refine ⟨8508351353167071442347857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5672234235444714294898571 8508351353167071442347857)
          ·
            refine ⟨6381263514875303581760893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8508351353167071442347857 6381263514875303581760893)
            ·
              refine ⟨2392973818078238843160335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6381263514875303581760893 2392973818078238843160335)
              ·
                refine ⟨3589460727117358264740503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2392973818078238843160335 3589460727117358264740503)
                ·
                  refine ⟨5384191090676037397110755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3589460727117358264740503 5384191090676037397110755)
                  ·
                    refine ⟨8076286636014056095666133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5384191090676037397110755 8076286636014056095666133)
                    ·
                      refine ⟨189287968031579439742175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8076286636014056095666133 189287968031579439742175)
                      ·
                        rfl

theorem cell23_368637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_368637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368637 prefixEnd_368637 := by exact prefixLift 368637
  have htrace : WordTrace (prefixWord ++ tailWord_368637) baseStart_368637 baseEnd_368637 := by
    simpa [prefixWord, tailWord_368637, baseEnd_368637] using wordTrace_append hprefix tailTrace_368637
  have hstable : (prefixWord ++ tailWord_368637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368637).length < 2 ^ (prefixWord ++ tailWord_368637).sum := by decide
  have hdescent : baseEnd_368637 < baseStart_368637 := by decide
  rcases family_descends (prefixWord ++ tailWord_368637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368646 : List Nat := [6, 2, 1, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_368646 : Nat := 118140960795 + 368646 * 2 ^ 59
def prefixEnd_368646 : Nat := 4983230072969 + 3 ^ 40 * 368646 * 2
def baseEnd_368646 : Nat := 189292589357469904529635

theorem tailTrace_368646 : CollatzResearch.WordTrace tailWord_368646 prefixEnd_368646 189292589357469904529635 := by
  unfold tailWord_368646
  simp only [CollatzResearch.WordTrace]
  refine ⟨420175756952061767794681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8963749481643984379619861 420175756952061767794681)
  ·
    refine ⟨315131817714046325846011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 420175756952061767794681 315131817714046325846011)
    ·
      refine ⟨472697726571069488769017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315131817714046325846011 472697726571069488769017)
      ·
        refine ⟨354523294928302116576763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472697726571069488769017 354523294928302116576763)
        ·
          refine ⟨531784942392453174865145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354523294928302116576763 531784942392453174865145)
          ·
            refine ⟨398838706794339881148859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531784942392453174865145 398838706794339881148859)
            ·
              refine ⟨598258060191509821723289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398838706794339881148859 598258060191509821723289)
              ·
                refine ⟨448693545143632366292467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598258060191509821723289 448693545143632366292467)
                ·
                  refine ⟨673040317715448549438701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448693545143632366292467 673040317715448549438701)
                  ·
                    refine ⟨252390119143293206039513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673040317715448549438701 252390119143293206039513)
                    ·
                      refine ⟨189292589357469904529635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 252390119143293206039513 189292589357469904529635)
                      ·
                        rfl

theorem cell23_368646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_368646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368646 prefixEnd_368646 := by exact prefixLift 368646
  have htrace : WordTrace (prefixWord ++ tailWord_368646) baseStart_368646 baseEnd_368646 := by
    simpa [prefixWord, tailWord_368646, baseEnd_368646] using wordTrace_append hprefix tailTrace_368646
  have hstable : (prefixWord ++ tailWord_368646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368646).length < 2 ^ (prefixWord ++ tailWord_368646).sum := by decide
  have hdescent : baseEnd_368646 < baseStart_368646 := by decide
  rcases family_descends (prefixWord ++ tailWord_368646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368661 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_368661 : Nat := 118140960795 + 368661 * 2 ^ 59
def prefixEnd_368661 : Nat := 4983230072969 + 3 ^ 40 * 368661 * 2
def baseEnd_368661 : Nat := 63100097189095781947355

theorem tailTrace_368661 : CollatzResearch.WordTrace tailWord_368661 prefixEnd_368661 63100097189095781947355 := by
  unfold tailWord_368661
  simp only [CollatzResearch.WordTrace]
  refine ⟨13446171317411634131225837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8964114211607756087483891 13446171317411634131225837)
  ·
    refine ⟨5042314244029362799209689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13446171317411634131225837 5042314244029362799209689)
    ·
      refine ⟨3781735683022022099407267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5042314244029362799209689 3781735683022022099407267)
      ·
        refine ⟨5672603524533033149110901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781735683022022099407267 5672603524533033149110901)
        ·
          refine ⟨531806580424971857729147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5672603524533033149110901 531806580424971857729147)
          ·
            refine ⟨797709870637457786593721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531806580424971857729147 797709870637457786593721)
            ·
              refine ⟨598282402978093339945291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797709870637457786593721 598282402978093339945291)
              ·
                refine ⟨897423604467140009917937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598282402978093339945291 897423604467140009917937)
                ·
                  refine ⟨673067703350355007438453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 897423604467140009917937 673067703350355007438453)
                  ·
                    refine ⟨63100097189095781947355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 673067703350355007438453 63100097189095781947355)
                    ·
                      rfl

theorem cell23_368661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_368661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368661 prefixEnd_368661 := by exact prefixLift 368661
  have htrace : WordTrace (prefixWord ++ tailWord_368661) baseStart_368661 baseEnd_368661 := by
    simpa [prefixWord, tailWord_368661, baseEnd_368661] using wordTrace_append hprefix tailTrace_368661
  have hstable : (prefixWord ++ tailWord_368661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368661).length < 2 ^ (prefixWord ++ tailWord_368661).sum := by decide
  have hdescent : baseEnd_368661 < baseStart_368661 := by decide
  rcases family_descends (prefixWord ++ tailWord_368661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368684 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_368684 : Nat := 118140960795 + 368684 * 2 ^ 59
def prefixEnd_368684 : Nat := 4983230072969 + 3 ^ 40 * 368684 * 2
def baseEnd_368684 : Nat := 189312101622340755854459

theorem tailTrace_368684 : CollatzResearch.WordTrace tailWord_368684 prefixEnd_368684 189312101622340755854459 := by
  unfold tailWord_368684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723505098164154529656553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8964673464218872706208737 6723505098164154529656553)
  ·
    refine ⟨5042628823623115897242415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6723505098164154529656553 5042628823623115897242415)
    ·
      refine ⟨7563943235434673845863623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5042628823623115897242415 7563943235434673845863623)
      ·
        refine ⟨11345914853152010768795435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7563943235434673845863623 11345914853152010768795435)
        ·
          refine ⟨17018872279728016153193153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11345914853152010768795435 17018872279728016153193153)
          ·
            refine ⟨12764154209796012114894865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17018872279728016153193153 12764154209796012114894865)
            ·
              refine ⟨9573115657347009086171149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12764154209796012114894865 9573115657347009086171149)
              ·
                refine ⟨3589918371505128407314181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9573115657347009086171149 3589918371505128407314181)
                ·
                  refine ⟨673109694657211576371409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3589918371505128407314181 673109694657211576371409)
                  ·
                    refine ⟨504832270992908682278557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673109694657211576371409 504832270992908682278557)
                    ·
                      refine ⟨189312101622340755854459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 504832270992908682278557 189312101622340755854459)
                      ·
                        rfl

theorem cell23_368684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_368684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368684 prefixEnd_368684 := by exact prefixLift 368684
  have htrace : WordTrace (prefixWord ++ tailWord_368684) baseStart_368684 baseEnd_368684 := by
    simpa [prefixWord, tailWord_368684, baseEnd_368684] using wordTrace_append hprefix tailTrace_368684
  have hstable : (prefixWord ++ tailWord_368684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368684).length < 2 ^ (prefixWord ++ tailWord_368684).sum := by decide
  have hdescent : baseEnd_368684 < baseStart_368684 := by decide
  rcases family_descends (prefixWord ++ tailWord_368684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368704 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 6]
def baseStart_368704 : Nat := 118140960795 + 368704 * 2 ^ 59
def prefixEnd_368704 : Nat := 4983230072969 + 3 ^ 40 * 368704 * 2
def baseEnd_368704 : Nat := 21035819026158964178263

theorem tailTrace_368704 : CollatzResearch.WordTrace tailWord_368704 prefixEnd_368704 21035819026158964178263 := by
  unfold tailWord_368704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723869828127926237520583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8965159770837234983360777 6723869828127926237520583)
  ·
    refine ⟨10085804742191889356280875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6723869828127926237520583 10085804742191889356280875)
    ·
      refine ⟨15128707113287834034421313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085804742191889356280875 15128707113287834034421313)
      ·
        refine ⟨11346530334965875525815985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15128707113287834034421313 11346530334965875525815985)
        ·
          refine ⟨8509897751224406644361989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11346530334965875525815985 8509897751224406644361989)
          ·
            refine ⟨1595605828354576245817873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8509897751224406644361989 1595605828354576245817873)
            ·
              refine ⟨1196704371265932184363405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1595605828354576245817873 1196704371265932184363405)
              ·
                refine ⟨448764139224724569136277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196704371265932184363405 448764139224724569136277)
                ·
                  refine ⟨21035819026158964178263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 448764139224724569136277 21035819026158964178263)
                  ·
                    rfl

theorem cell23_368704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 6].length) (baseStart_368704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368704 prefixEnd_368704 := by exact prefixLift 368704
  have htrace : WordTrace (prefixWord ++ tailWord_368704) baseStart_368704 baseEnd_368704 := by
    simpa [prefixWord, tailWord_368704, baseEnd_368704] using wordTrace_append hprefix tailTrace_368704
  have hstable : (prefixWord ++ tailWord_368704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368704).length < 2 ^ (prefixWord ++ tailWord_368704).sum := by decide
  have hdescent : baseEnd_368704 < baseStart_368704 := by decide
  rcases family_descends (prefixWord ++ tailWord_368704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368707 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6]
def baseStart_368707 : Nat := 118140960795 + 368707 * 2 ^ 59
def prefixEnd_368707 : Nat := 4983230072969 + 3 ^ 40 * 368707 * 2
def baseEnd_368707 : Nat := 189323911677394165866853

theorem tailTrace_368707 : CollatzResearch.WordTrace tailWord_368707 prefixEnd_368707 189323911677394165866853 := by
  unfold tailWord_368707
  simp only [CollatzResearch.WordTrace]
  refine ⟨13447849075244983987400375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8965232716829989324933583 13447849075244983987400375)
  ·
    refine ⟨20171773612867475981100563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13447849075244983987400375 20171773612867475981100563)
    ·
      refine ⟨30257660419301213971650845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20171773612867475981100563 30257660419301213971650845)
      ·
        refine ⟨11346622657237955239369067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30257660419301213971650845 11346622657237955239369067)
        ·
          refine ⟨17019933985856932859053601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11346622657237955239369067 17019933985856932859053601)
          ·
            refine ⟨12764950489392699644290201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17019933985856932859053601 12764950489392699644290201)
            ·
              refine ⟨9573712867044524733217651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12764950489392699644290201 9573712867044524733217651)
              ·
                refine ⟨14360569300566787099826477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9573712867044524733217651 14360569300566787099826477)
                ·
                  refine ⟨5385213487712545162434929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14360569300566787099826477 5385213487712545162434929)
                  ·
                    refine ⟨4038910115784408871826197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5385213487712545162434929 4038910115784408871826197)
                    ·
                      refine ⟨189323911677394165866853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4038910115784408871826197 189323911677394165866853)
                      ·
                        rfl

theorem cell23_368707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_368707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368707 prefixEnd_368707 := by exact prefixLift 368707
  have htrace : WordTrace (prefixWord ++ tailWord_368707) baseStart_368707 baseEnd_368707 := by
    simpa [prefixWord, tailWord_368707, baseEnd_368707] using wordTrace_append hprefix tailTrace_368707
  have hstable : (prefixWord ++ tailWord_368707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368707).length < 2 ^ (prefixWord ++ tailWord_368707).sum := by decide
  have hdescent : baseEnd_368707 < baseStart_368707 := by decide
  rcases family_descends (prefixWord ++ tailWord_368707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368718 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_368718 : Nat := 118140960795 + 368718 * 2 ^ 59
def prefixEnd_368718 : Nat := 4983230072969 + 3 ^ 40 * 368718 * 2
def baseEnd_368718 : Nat := 189329559964593622829303

theorem tailTrace_368718 : CollatzResearch.WordTrace tailWord_368718 prefixEnd_368718 189329559964593622829303 := by
  unfold tailWord_368718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1681031284775641608256351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8965500185470088577367205 1681031284775641608256351)
  ·
    refine ⟨2521546927163462412384527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1681031284775641608256351 2521546927163462412384527)
    ·
      refine ⟨3782320390745193618576791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2521546927163462412384527 3782320390745193618576791)
      ·
        refine ⟨5673480586117790427865187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3782320390745193618576791 5673480586117790427865187)
        ·
          refine ⟨8510220879176685641797781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5673480586117790427865187 8510220879176685641797781)
          ·
            refine ⟨398916603711407139459271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8510220879176685641797781 398916603711407139459271)
            ·
              refine ⟨598374905567110709188907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398916603711407139459271 598374905567110709188907)
              ·
                refine ⟨897562358350666063783361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598374905567110709188907 897562358350666063783361)
                ·
                  refine ⟨673171768762999547837521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 897562358350666063783361 673171768762999547837521)
                  ·
                    refine ⟨504878826572249660878141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673171768762999547837521 504878826572249660878141)
                    ·
                      refine ⟨189329559964593622829303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 504878826572249660878141 189329559964593622829303)
                      ·
                        rfl

theorem cell23_368718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_368718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368718 prefixEnd_368718 := by exact prefixLift 368718
  have htrace : WordTrace (prefixWord ++ tailWord_368718) baseStart_368718 baseEnd_368718 := by
    simpa [prefixWord, tailWord_368718, baseEnd_368718] using wordTrace_append hprefix tailTrace_368718
  have hstable : (prefixWord ++ tailWord_368718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368718).length < 2 ^ (prefixWord ++ tailWord_368718).sum := by decide
  have hdescent : baseEnd_368718 < baseStart_368718 := by decide
  rcases family_descends (prefixWord ++ tailWord_368718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368747 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 12]
def baseStart_368747 : Nat := 118140960795 + 368747 * 2 ^ 59
def prefixEnd_368747 : Nat := 4983230072969 + 3 ^ 40 * 368747 * 2
def baseEnd_368747 : Nat := 63114816967858003122223

theorem tailTrace_368747 : CollatzResearch.WordTrace tailWord_368747 prefixEnd_368747 63114816967858003122223 := by
  unfold tailWord_368747
  simp only [CollatzResearch.WordTrace]
  refine ⟨13449307995100070818856495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8966205330066713879237663 13449307995100070818856495)
  ·
    refine ⟨20173961992650106228284743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13449307995100070818856495 20173961992650106228284743)
    ·
      refine ⟨30260942988975159342427115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20173961992650106228284743 30260942988975159342427115)
      ·
        refine ⟨45391414483462739013640673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30260942988975159342427115 45391414483462739013640673)
        ·
          refine ⟨34043560862597054260230505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45391414483462739013640673 34043560862597054260230505)
          ·
            refine ⟨25532670646947790695172879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34043560862597054260230505 25532670646947790695172879)
            ·
              refine ⟨38299005970421686042759319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25532670646947790695172879 38299005970421686042759319)
              ·
                refine ⟨57448508955632529064138979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38299005970421686042759319 57448508955632529064138979)
                ·
                  refine ⟨86172763433448793596208469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57448508955632529064138979 86172763433448793596208469)
                  ·
                    refine ⟨63114816967858003122223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 86172763433448793596208469 63114816967858003122223)
                    ·
                      rfl

theorem cell23_368747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_368747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368747 prefixEnd_368747 := by exact prefixLift 368747
  have htrace : WordTrace (prefixWord ++ tailWord_368747) baseStart_368747 baseEnd_368747 := by
    simpa [prefixWord, tailWord_368747, baseEnd_368747] using wordTrace_append hprefix tailTrace_368747
  have hstable : (prefixWord ++ tailWord_368747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368747).length < 2 ^ (prefixWord ++ tailWord_368747).sum := by decide
  have hdescent : baseEnd_368747 < baseStart_368747 := by decide
  rcases family_descends (prefixWord ++ tailWord_368747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368748 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_368748 : Nat := 118140960795 + 368748 * 2 ^ 59
def prefixEnd_368748 : Nat := 4983230072969 + 3 ^ 40 * 368748 * 2
def baseEnd_368748 : Nat := 189344964384228505454165

theorem tailTrace_368748 : CollatzResearch.WordTrace tailWord_368748 prefixEnd_368748 189344964384228505454165 := by
  unfold tailWord_368748
  simp only [CollatzResearch.WordTrace]
  refine ⟨6724672234048223994821449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8966229645397631993095265 6724672234048223994821449)
  ·
    refine ⟨5043504175536167996116087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6724672234048223994821449 5043504175536167996116087)
    ·
      refine ⟨7565256263304251994174131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5043504175536167996116087 7565256263304251994174131)
      ·
        refine ⟨11347884394956377991261197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7565256263304251994174131 11347884394956377991261197)
        ·
          refine ⟨4255456648108641746722949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11347884394956377991261197 4255456648108641746722949)
          ·
            refine ⟨797898121520370327510553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4255456648108641746722949 797898121520370327510553)
            ·
              refine ⟨598423591140277745632915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797898121520370327510553 598423591140277745632915)
              ·
                refine ⟨897635386710416618449373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598423591140277745632915 897635386710416618449373)
                ·
                  refine ⟨336613270016406231918515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897635386710416618449373 336613270016406231918515)
                  ·
                    refine ⟨504919905024609347877773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336613270016406231918515 504919905024609347877773)
                    ·
                      refine ⟨189344964384228505454165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 504919905024609347877773 189344964384228505454165)
                      ·
                        rfl

theorem cell23_368748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_368748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368748 prefixEnd_368748 := by exact prefixLift 368748
  have htrace : WordTrace (prefixWord ++ tailWord_368748) baseStart_368748 baseEnd_368748 := by
    simpa [prefixWord, tailWord_368748, baseEnd_368748] using wordTrace_append hprefix tailTrace_368748
  have hstable : (prefixWord ++ tailWord_368748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368748).length < 2 ^ (prefixWord ++ tailWord_368748).sum := by decide
  have hdescent : baseEnd_368748 < baseStart_368748 := by decide
  rcases family_descends (prefixWord ++ tailWord_368748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368758 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_368758 : Nat := 118140960795 + 368758 * 2 ^ 59
def prefixEnd_368758 : Nat := 4983230072969 + 3 ^ 40 * 368758 * 2
def baseEnd_368758 : Nat := 189350099190773466329119

theorem tailTrace_368758 : CollatzResearch.WordTrace tailWord_368758 prefixEnd_368758 189350099190773466329119 := by
  unfold tailWord_368758
  simp only [CollatzResearch.WordTrace]
  refine ⟨840606824878763731094183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8966472798706813131671285 840606824878763731094183)
  ·
    refine ⟨1260910237318145596641275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840606824878763731094183 1260910237318145596641275)
    ·
      refine ⟨1891365355977218394961913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260910237318145596641275 1891365355977218394961913)
      ·
        refine ⟨1418524016982913796221435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1891365355977218394961913 1418524016982913796221435)
        ·
          refine ⟨2127786025474370694332153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418524016982913796221435 2127786025474370694332153)
          ·
            refine ⟨1595839519105778020749115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2127786025474370694332153 1595839519105778020749115)
            ·
              refine ⟨2393759278658667031123673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595839519105778020749115 2393759278658667031123673)
              ·
                refine ⟨1795319458994000273342755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393759278658667031123673 1795319458994000273342755)
                ·
                  refine ⟨2692979188491000410014133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1795319458994000273342755 2692979188491000410014133)
                  ·
                    refine ⟨252466798921031288438825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2692979188491000410014133 252466798921031288438825)
                    ·
                      refine ⟨189350099190773466329119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 252466798921031288438825 189350099190773466329119)
                      ·
                        rfl

theorem cell23_368758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_368758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368758 prefixEnd_368758 := by exact prefixLift 368758
  have htrace : WordTrace (prefixWord ++ tailWord_368758) baseStart_368758 baseEnd_368758 := by
    simpa [prefixWord, tailWord_368758, baseEnd_368758] using wordTrace_append hprefix tailTrace_368758
  have hstable : (prefixWord ++ tailWord_368758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368758).length < 2 ^ (prefixWord ++ tailWord_368758).sum := by decide
  have hdescent : baseEnd_368758 < baseStart_368758 := by decide
  rcases family_descends (prefixWord ++ tailWord_368758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368771 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 4]
def baseStart_368771 : Nat := 118140960795 + 368771 * 2 ^ 59
def prefixEnd_368771 : Nat := 4983230072969 + 3 ^ 40 * 368771 * 2
def baseEnd_368771 : Nat := 189356774439281915466559

theorem tailTrace_368771 : CollatzResearch.WordTrace tailWord_368771 prefixEnd_368771 189356774439281915466559 := by
  unfold tailWord_368771
  simp only [CollatzResearch.WordTrace]
  refine ⟨13450183347013122917730167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8966788898008748611820111 13450183347013122917730167)
  ·
    refine ⟨20175275020519684376595251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13450183347013122917730167 20175275020519684376595251)
    ·
      refine ⟨30262912530779526564892877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20175275020519684376595251 30262912530779526564892877)
      ·
        refine ⟨11348592199042322461834829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30262912530779526564892877 11348592199042322461834829)
        ·
          refine ⟨4255722074640870923188061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11348592199042322461834829 4255722074640870923188061)
          ·
            refine ⟨1595895777990326596195523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4255722074640870923188061 1595895777990326596195523)
            ·
              refine ⟨2393843666985489894293285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595895777990326596195523 2393843666985489894293285)
              ·
                refine ⟨448845687559779355179991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2393843666985489894293285 448845687559779355179991)
                ·
                  refine ⟨673268531339669032769987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448845687559779355179991 673268531339669032769987)
                  ·
                    refine ⟨1009902797009503549154981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 673268531339669032769987 1009902797009503549154981)
                    ·
                      refine ⟨189356774439281915466559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1009902797009503549154981 189356774439281915466559)
                      ·
                        rfl

theorem cell23_368771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_368771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368771 prefixEnd_368771 := by exact prefixLift 368771
  have htrace : WordTrace (prefixWord ++ tailWord_368771) baseStart_368771 baseEnd_368771 := by
    simpa [prefixWord, tailWord_368771, baseEnd_368771] using wordTrace_append hprefix tailTrace_368771
  have hstable : (prefixWord ++ tailWord_368771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368771).length < 2 ^ (prefixWord ++ tailWord_368771).sum := by decide
  have hdescent : baseEnd_368771 < baseStart_368771 := by decide
  rcases family_descends (prefixWord ++ tailWord_368771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368784 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_368784 : Nat := 118140960795 + 368784 * 2 ^ 59
def prefixEnd_368784 : Nat := 4983230072969 + 3 ^ 40 * 368784 * 2
def baseEnd_368784 : Nat := 189363449687790364603999

theorem tailTrace_368784 : CollatzResearch.WordTrace tailWord_368784 prefixEnd_368784 189363449687790364603999 := by
  unfold tailWord_368784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725328747983013068976703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8967104997310684091968937 6725328747983013068976703)
  ·
    refine ⟨10087993121974519603465055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6725328747983013068976703 10087993121974519603465055)
    ·
      refine ⟨15131989682961779405197583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10087993121974519603465055 15131989682961779405197583)
      ·
        refine ⟨22697984524442669107796375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15131989682961779405197583 22697984524442669107796375)
        ·
          refine ⟨34046976786664003661694563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22697984524442669107796375 34046976786664003661694563)
          ·
            refine ⟨51070465179996005492541845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34046976786664003661694563 51070465179996005492541845)
            ·
              refine ⟨2393928055312312757462899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51070465179996005492541845 2393928055312312757462899)
              ·
                refine ⟨3590892082968469136194349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393928055312312757462899 3590892082968469136194349)
                ·
                  refine ⟨1346584531113175926072881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3590892082968469136194349 1346584531113175926072881)
                  ·
                    refine ⟨1009938398334881944554661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1346584531113175926072881 1009938398334881944554661)
                    ·
                      refine ⟨189363449687790364603999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1009938398334881944554661 189363449687790364603999)
                      ·
                        rfl

theorem cell23_368784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_368784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368784 prefixEnd_368784 := by exact prefixLift 368784
  have htrace : WordTrace (prefixWord ++ tailWord_368784) baseStart_368784 baseEnd_368784 := by
    simpa [prefixWord, tailWord_368784, baseEnd_368784] using wordTrace_append hprefix tailTrace_368784
  have hstable : (prefixWord ++ tailWord_368784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368784).length < 2 ^ (prefixWord ++ tailWord_368784).sum := by decide
  have hdescent : baseEnd_368784 < baseStart_368784 := by decide
  rcases family_descends (prefixWord ++ tailWord_368784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368871 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 1, 8]
def baseStart_368871 : Nat := 118140960795 + 368871 * 2 ^ 59
def prefixEnd_368871 : Nat := 4983230072969 + 3 ^ 40 * 368871 * 2
def baseEnd_368871 : Nat := 63136040834910508072033

theorem tailTrace_368871 : CollatzResearch.WordTrace tailWord_368871 prefixEnd_368871 63136040834910508072033 := by
  unfold tailWord_368871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13453830646650839996370467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8969220431100559997580311 13453830646650839996370467)
  ·
    refine ⟨20180745969976259994555701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13453830646650839996370467 20180745969976259994555701)
    ·
      refine ⟨1891944934685274374489597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20180745969976259994555701 1891944934685274374489597)
      ·
        refine ⟨709479350506977890433599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1891944934685274374489597 709479350506977890433599)
        ·
          refine ⟨1064219025760466835650399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709479350506977890433599 1064219025760466835650399)
          ·
            refine ⟨1596328538640700253475599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064219025760466835650399 1596328538640700253475599)
            ·
              refine ⟨2394492807961050380213399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596328538640700253475599 2394492807961050380213399)
              ·
                refine ⟨3591739211941575570320099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2394492807961050380213399 3591739211941575570320099)
                ·
                  refine ⟨5387608817912363355480149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3591739211941575570320099 5387608817912363355480149)
                  ·
                    refine ⟨63136040834910508072033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5387608817912363355480149 63136040834910508072033)
                    ·
                      rfl

theorem cell23_368871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_368871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368871 prefixEnd_368871 := by exact prefixLift 368871
  have htrace : WordTrace (prefixWord ++ tailWord_368871) baseStart_368871 baseEnd_368871 := by
    simpa [prefixWord, tailWord_368871, baseEnd_368871] using wordTrace_append hprefix tailTrace_368871
  have hstable : (prefixWord ++ tailWord_368871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368871).length < 2 ^ (prefixWord ++ tailWord_368871).sum := by decide
  have hdescent : baseEnd_368871 < baseStart_368871 := by decide
  rcases family_descends (prefixWord ++ tailWord_368871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368928 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3]
def baseStart_368928 : Nat := 118140960795 + 368928 * 2 ^ 59
def prefixEnd_368928 : Nat := 4983230072969 + 3 ^ 40 * 368928 * 2
def baseEnd_368928 : Nat := 189437390902037801203337

theorem tailTrace_368928 : CollatzResearch.WordTrace tailWord_368928 prefixEnd_368928 189437390902037801203337 := by
  unfold tailWord_368928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727954803722169365597719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8970606404962892487463625 6727954803722169365597719)
  ·
    refine ⟨10091932205583254048396579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727954803722169365597719 10091932205583254048396579)
    ·
      refine ⟨15137898308374881072594869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10091932205583254048396579 15137898308374881072594869)
      ·
        refine ⟨1419177966410145100555769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15137898308374881072594869 1419177966410145100555769)
        ·
          refine ⟨1064383474807608825416827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419177966410145100555769 1064383474807608825416827)
          ·
            refine ⟨1596575212211413238125241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064383474807608825416827 1596575212211413238125241)
            ·
              refine ⟨1197431409158559928593931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596575212211413238125241 1197431409158559928593931)
              ·
                refine ⟨1796147113737839892890897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197431409158559928593931 1796147113737839892890897)
                ·
                  refine ⟨1347110335303379919668173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796147113737839892890897 1347110335303379919668173)
                  ·
                    refine ⟨505166375738767469875565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1347110335303379919668173 505166375738767469875565)
                    ·
                      refine ⟨189437390902037801203337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505166375738767469875565 189437390902037801203337)
                      ·
                        rfl

theorem cell23_368928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_368928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368928 prefixEnd_368928 := by exact prefixLift 368928
  have htrace : WordTrace (prefixWord ++ tailWord_368928) baseStart_368928 baseEnd_368928 := by
    simpa [prefixWord, tailWord_368928, baseEnd_368928] using wordTrace_append hprefix tailTrace_368928
  have hstable : (prefixWord ++ tailWord_368928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368928).length < 2 ^ (prefixWord ++ tailWord_368928).sum := by decide
  have hdescent : baseEnd_368928 < baseStart_368928 := by decide
  rcases family_descends (prefixWord ++ tailWord_368928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368948 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_368948 : Nat := 118140960795 + 368948 * 2 ^ 59
def prefixEnd_368948 : Nat := 4983230072969 + 3 ^ 40 * 368948 * 2
def baseEnd_368948 : Nat := 63149220171709240984415

theorem tailTrace_368948 : CollatzResearch.WordTrace tailWord_368948 prefixEnd_368948 63149220171709240984415 := by
  unfold tailWord_368948
  simp only [CollatzResearch.WordTrace]
  refine ⟨6728319533685941073461749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8971092711581254764615665 6728319533685941073461749)
  ·
    refine ⟨630779956283056975637039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6728319533685941073461749 630779956283056975637039)
    ·
      refine ⟨946169934424585463455559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630779956283056975637039 946169934424585463455559)
      ·
        refine ⟨1419254901636878195183339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946169934424585463455559 1419254901636878195183339)
        ·
          refine ⟨2128882352455317292775009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419254901636878195183339 2128882352455317292775009)
          ·
            refine ⟨1596661764341487969581257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2128882352455317292775009 1596661764341487969581257)
            ·
              refine ⟨1197496323256115977185943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596661764341487969581257 1197496323256115977185943)
              ·
                refine ⟨1796244484884173965778915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197496323256115977185943 1796244484884173965778915)
                ·
                  refine ⟨2694366727326260948668373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1796244484884173965778915 2694366727326260948668373)
                  ·
                    refine ⟨63149220171709240984415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2694366727326260948668373 63149220171709240984415)
                    ·
                      rfl

theorem cell23_368948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_368948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368948 prefixEnd_368948 := by exact prefixLift 368948
  have htrace : WordTrace (prefixWord ++ tailWord_368948) baseStart_368948 baseEnd_368948 := by
    simpa [prefixWord, tailWord_368948, baseEnd_368948] using wordTrace_append hprefix tailTrace_368948
  have hstable : (prefixWord ++ tailWord_368948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368948).length < 2 ^ (prefixWord ++ tailWord_368948).sum := by decide
  have hdescent : baseEnd_368948 < baseStart_368948 := by decide
  rcases family_descends (prefixWord ++ tailWord_368948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368951 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_368951 : Nat := 118140960795 + 368951 * 2 ^ 59
def prefixEnd_368951 : Nat := 4983230072969 + 3 ^ 40 * 368951 * 2
def baseEnd_368951 : Nat := 189449200957091211215731

theorem tailTrace_368951 : CollatzResearch.WordTrace tailWord_368951 prefixEnd_368951 189449200957091211215731 := by
  unfold tailWord_368951
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456748486361013659282707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971165657574009106188471 13456748486361013659282707)
  ·
    refine ⟨20185122729541520488924061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13456748486361013659282707 20185122729541520488924061)
    ·
      refine ⟨7569421023578070183346523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20185122729541520488924061 7569421023578070183346523)
      ·
        refine ⟨11354131535367105275019785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7569421023578070183346523 11354131535367105275019785)
        ·
          refine ⟨8515598651525328956264839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11354131535367105275019785 8515598651525328956264839)
          ·
            refine ⟨12773397977287993434397259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8515598651525328956264839 12773397977287993434397259)
            ·
              refine ⟨19160096965931990151595889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12773397977287993434397259 19160096965931990151595889)
              ·
                refine ⟨14370072724448992613696917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19160096965931990151595889 14370072724448992613696917)
                ·
                  refine ⟨673597158958546528767043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14370072724448992613696917 673597158958546528767043)
                  ·
                    refine ⟨1010395738437819793150565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 673597158958546528767043 1010395738437819793150565)
                    ·
                      refine ⟨189449200957091211215731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1010395738437819793150565 189449200957091211215731)
                      ·
                        rfl

theorem cell23_368951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_368951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368951 prefixEnd_368951 := by exact prefixLift 368951
  have htrace : WordTrace (prefixWord ++ tailWord_368951) baseStart_368951 baseEnd_368951 := by
    simpa [prefixWord, tailWord_368951, baseEnd_368951] using wordTrace_append hprefix tailTrace_368951
  have hstable : (prefixWord ++ tailWord_368951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368951).length < 2 ^ (prefixWord ++ tailWord_368951).sum := by decide
  have hdescent : baseEnd_368951 < baseStart_368951 := by decide
  rcases family_descends (prefixWord ++ tailWord_368951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368968 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_368968 : Nat := 118140960795 + 368968 * 2 ^ 59
def prefixEnd_368968 : Nat := 4983230072969 + 3 ^ 40 * 368968 * 2
def baseEnd_368968 : Nat := 189457930128217644703153

theorem tailTrace_368968 : CollatzResearch.WordTrace tailWord_368968 prefixEnd_368968 189457930128217644703153 := by
  unfold tailWord_368968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6728684263649712781325779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8971579018199617041767705 6728684263649712781325779)
  ·
    refine ⟨10093026395474569171988669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6728684263649712781325779 10093026395474569171988669)
    ·
      refine ⟨3784884898302963439495751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10093026395474569171988669 3784884898302963439495751)
      ·
        refine ⟨5677327347454445159243627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784884898302963439495751 5677327347454445159243627)
        ·
          refine ⟨8515991021181667738865441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5677327347454445159243627 8515991021181667738865441)
          ·
            refine ⟨6386993265886250804149081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8515991021181667738865441 6386993265886250804149081)
            ·
              refine ⟨4790244949414688103111811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6386993265886250804149081 4790244949414688103111811)
              ·
                refine ⟨7185367424122032154667717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4790244949414688103111811 7185367424122032154667717)
                ·
                  refine ⟨1347256392022881029000197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7185367424122032154667717 1347256392022881029000197)
                  ·
                    refine ⟨252610573504290192937537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347256392022881029000197 252610573504290192937537)
                    ·
                      refine ⟨189457930128217644703153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 252610573504290192937537 189457930128217644703153)
                      ·
                        rfl

theorem cell23_368968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_368968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368968 prefixEnd_368968 := by exact prefixLift 368968
  have htrace : WordTrace (prefixWord ++ tailWord_368968) baseStart_368968 baseEnd_368968 := by
    simpa [prefixWord, tailWord_368968, baseEnd_368968] using wordTrace_append hprefix tailTrace_368968
  have hstable : (prefixWord ++ tailWord_368968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368968).length < 2 ^ (prefixWord ++ tailWord_368968).sum := by decide
  have hdescent : baseEnd_368968 < baseStart_368968 := by decide
  rcases family_descends (prefixWord ++ tailWord_368968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_368971 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 3]
def baseStart_368971 : Nat := 118140960795 + 368971 * 2 ^ 59
def prefixEnd_368971 : Nat := 4983230072969 + 3 ^ 40 * 368971 * 2
def baseEnd_368971 : Nat := 189459470570181132965639

theorem tailTrace_368971 : CollatzResearch.WordTrace tailWord_368971 prefixEnd_368971 189459470570181132965639 := by
  unfold tailWord_368971
  simp only [CollatzResearch.WordTrace]
  refine ⟨13457477946288557075010767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8971651964192371383340511 13457477946288557075010767)
  ·
    refine ⟨20186216919432835612516151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13457477946288557075010767 20186216919432835612516151)
    ·
      refine ⟨30279325379149253418774227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20186216919432835612516151 30279325379149253418774227)
      ·
        refine ⟨45418988068723880128161341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30279325379149253418774227 45418988068723880128161341)
        ·
          refine ⟨17032120525771455048060503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45418988068723880128161341 17032120525771455048060503)
          ·
            refine ⟨25548180788657182572090755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17032120525771455048060503 25548180788657182572090755)
            ·
              refine ⟨38322271182985773858136133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25548180788657182572090755 38322271182985773858136133)
              ·
                refine ⟨7185425846809832598400525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38322271182985773858136133 7185425846809832598400525)
                ·
                  refine ⟨2694534692553687224400197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7185425846809832598400525 2694534692553687224400197)
                  ·
                    refine ⟨505225254853816354575037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2694534692553687224400197 505225254853816354575037)
                    ·
                      refine ⟨189459470570181132965639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505225254853816354575037 189459470570181132965639)
                      ·
                        rfl

theorem cell23_368971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 3].length) (baseStart_368971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_368971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_368971 prefixEnd_368971 := by exact prefixLift 368971
  have htrace : WordTrace (prefixWord ++ tailWord_368971) baseStart_368971 baseEnd_368971 := by
    simpa [prefixWord, tailWord_368971, baseEnd_368971] using wordTrace_append hprefix tailTrace_368971
  have hstable : (prefixWord ++ tailWord_368971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_368971).length < 2 ^ (prefixWord ++ tailWord_368971).sum := by decide
  have hdescent : baseEnd_368971 < baseStart_368971 := by decide
  rcases family_descends (prefixWord ++ tailWord_368971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369005 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_369005 : Nat := 118140960795 + 369005 * 2 ^ 59
def prefixEnd_369005 : Nat := 4983230072969 + 3 ^ 40 * 369005 * 2
def baseEnd_369005 : Nat := 189476928912433999940483

theorem tailTrace_369005 : CollatzResearch.WordTrace tailWord_369005 prefixEnd_369005 189476928912433999940483 := by
  unfold tailWord_369005
  simp only [CollatzResearch.WordTrace]
  refine ⟨13458718028165380881748469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8972478685443587254498979 13458718028165380881748469)
  ·
    refine ⟨1261754815140504457663919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13458718028165380881748469 1261754815140504457663919)
    ·
      refine ⟨1892632222710756686495879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261754815140504457663919 1892632222710756686495879)
      ·
        refine ⟨2838948334066135029743819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892632222710756686495879 2838948334066135029743819)
        ·
          refine ⟨4258422501099202544615729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838948334066135029743819 4258422501099202544615729)
          ·
            refine ⟨3193816875824401908461797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4258422501099202544615729 3193816875824401908461797)
            ·
              refine ⟨598840664217075357836587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3193816875824401908461797 598840664217075357836587)
              ·
                refine ⟨898260996325613036754881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598840664217075357836587 898260996325613036754881)
                ·
                  refine ⟨673695747244209777566161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 898260996325613036754881 673695747244209777566161)
                  ·
                    refine ⟨505271810433157333174621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 673695747244209777566161 505271810433157333174621)
                    ·
                      refine ⟨189476928912433999940483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505271810433157333174621 189476928912433999940483)
                      ·
                        rfl

theorem cell23_369005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_369005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369005 prefixEnd_369005 := by exact prefixLift 369005
  have htrace : WordTrace (prefixWord ++ tailWord_369005) baseStart_369005 baseEnd_369005 := by
    simpa [prefixWord, tailWord_369005, baseEnd_369005] using wordTrace_append hprefix tailTrace_369005
  have hstable : (prefixWord ++ tailWord_369005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369005).length < 2 ^ (prefixWord ++ tailWord_369005).sum := by decide
  have hdescent : baseEnd_369005 < baseStart_369005 := by decide
  rcases family_descends (prefixWord ++ tailWord_369005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369025 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 6]
def baseStart_369025 : Nat := 118140960795 + 369025 * 2 ^ 59
def prefixEnd_369025 : Nat := 4983230072969 + 3 ^ 40 * 369025 * 2
def baseEnd_369025 : Nat := 21054133169502657965599

theorem tailTrace_369025 : CollatzResearch.WordTrace tailWord_369025 prefixEnd_369025 21054133169502657965599 := by
  unfold tailWord_369025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459447488092924297476529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8972964992061949531651019 13459447488092924297476529)
  ·
    refine ⟨10094585616069693223107397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13459447488092924297476529 10094585616069693223107397)
    ·
      refine ⟨1892734803013067479332637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10094585616069693223107397 1892734803013067479332637)
      ·
        refine ⟨709775551129900304749739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1892734803013067479332637 709775551129900304749739)
        ·
          refine ⟨1064663326694850457124609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709775551129900304749739 1064663326694850457124609)
          ·
            refine ⟨798497495021137842843457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064663326694850457124609 798497495021137842843457)
            ·
              refine ⟨598873121265853382132593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798497495021137842843457 598873121265853382132593)
              ·
                refine ⟨449154840949390036599445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598873121265853382132593 449154840949390036599445)
                ·
                  refine ⟨21054133169502657965599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 449154840949390036599445 21054133169502657965599)
                  ·
                    rfl

theorem cell23_369025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 6].length) (baseStart_369025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369025 prefixEnd_369025 := by exact prefixLift 369025
  have htrace : WordTrace (prefixWord ++ tailWord_369025) baseStart_369025 baseEnd_369025 := by
    simpa [prefixWord, tailWord_369025, baseEnd_369025] using wordTrace_append hprefix tailTrace_369025
  have hstable : (prefixWord ++ tailWord_369025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369025).length < 2 ^ (prefixWord ++ tailWord_369025).sum := by decide
  have hdescent : baseEnd_369025 < baseStart_369025 := by decide
  rcases family_descends (prefixWord ++ tailWord_369025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369041 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_369041 : Nat := 118140960795 + 369041 * 2 ^ 59
def prefixEnd_369041 : Nat := 4983230072969 + 3 ^ 40 * 369041 * 2
def baseEnd_369041 : Nat := 189495414215995859090317

theorem tailTrace_369041 : CollatzResearch.WordTrace tailWord_369041 prefixEnd_369041 189495414215995859090317 := by
  unfold tailWord_369041
  simp only [CollatzResearch.WordTrace]
  refine ⟨13460031056034959030058977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8973354037356639353372651 13460031056034959030058977)
  ·
    refine ⟨10095023292026219272544233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13460031056034959030058977 10095023292026219272544233)
    ·
      refine ⟨7571267469019664454408175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10095023292026219272544233 7571267469019664454408175)
      ·
        refine ⟨11356901203529496681612263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7571267469019664454408175 11356901203529496681612263)
        ·
          refine ⟨17035351805294245022418395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11356901203529496681612263 17035351805294245022418395)
          ·
            refine ⟨25553027707941367533627593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17035351805294245022418395 25553027707941367533627593)
            ·
              refine ⟨19164770780956025650220695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25553027707941367533627593 19164770780956025650220695)
              ·
                refine ⟨28747156171434038475331043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19164770780956025650220695 28747156171434038475331043)
                ·
                  refine ⟨43120734257151057712996565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28747156171434038475331043 43120734257151057712996565)
                  ·
                    refine ⟨1010642209151977915148357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43120734257151057712996565 1010642209151977915148357)
                    ·
                      refine ⟨189495414215995859090317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1010642209151977915148357 189495414215995859090317)
                      ·
                        rfl

theorem cell23_369041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_369041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369041 prefixEnd_369041 := by exact prefixLift 369041
  have htrace : WordTrace (prefixWord ++ tailWord_369041) baseStart_369041 baseEnd_369041 := by
    simpa [prefixWord, tailWord_369041, baseEnd_369041] using wordTrace_append hprefix tailTrace_369041
  have hstable : (prefixWord ++ tailWord_369041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369041).length < 2 ^ (prefixWord ++ tailWord_369041).sum := by decide
  have hdescent : baseEnd_369041 < baseStart_369041 := by decide
  rcases family_descends (prefixWord ++ tailWord_369041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369046 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_369046 : Nat := 118140960795 + 369046 * 2 ^ 59
def prefixEnd_369046 : Nat := 4983230072969 + 3 ^ 40 * 369046 * 2
def baseEnd_369046 : Nat := 63165993873089446509265

theorem tailTrace_369046 : CollatzResearch.WordTrace tailWord_369046 prefixEnd_369046 63165993873089446509265 := by
  unfold tailWord_369046
  simp only [CollatzResearch.WordTrace]
  refine ⟨841263338813552805249437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8973475614011229922660661 841263338813552805249437)
  ·
    refine ⟨315473752055082301968539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 841263338813552805249437 315473752055082301968539)
    ·
      refine ⟨473210628082623452952809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315473752055082301968539 473210628082623452952809)
      ·
        refine ⟨354907971061967589714607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473210628082623452952809 354907971061967589714607)
        ·
          refine ⟨532361956592951384571911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354907971061967589714607 532361956592951384571911)
          ·
            refine ⟨798542934889427076857867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532361956592951384571911 798542934889427076857867)
            ·
              refine ⟨1197814402334140615286801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798542934889427076857867 1197814402334140615286801)
              ·
                refine ⟨898360801750605461465101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197814402334140615286801 898360801750605461465101)
                ·
                  refine ⟨336885300656477048049413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898360801750605461465101 336885300656477048049413)
                  ·
                    refine ⟨63165993873089446509265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336885300656477048049413 63165993873089446509265)
                    ·
                      rfl

theorem cell23_369046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_369046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369046 prefixEnd_369046 := by exact prefixLift 369046
  have htrace : WordTrace (prefixWord ++ tailWord_369046) baseStart_369046 baseEnd_369046 := by
    simpa [prefixWord, tailWord_369046, baseEnd_369046] using wordTrace_append hprefix tailTrace_369046
  have hstable : (prefixWord ++ tailWord_369046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369046).length < 2 ^ (prefixWord ++ tailWord_369046).sum := by decide
  have hdescent : baseEnd_369046 < baseStart_369046 := by decide
  rcases family_descends (prefixWord ++ tailWord_369046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369068 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_369068 : Nat := 118140960795 + 369068 * 2 ^ 59
def prefixEnd_369068 : Nat := 4983230072969 + 3 ^ 40 * 369068 * 2
def baseEnd_369068 : Nat := 63169759397889084484231

theorem tailTrace_369068 : CollatzResearch.WordTrace tailWord_369068 prefixEnd_369068 63169759397889084484231 := by
  unfold tailWord_369068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6730507913468571320645929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8974010551291428427527905 6730507913468571320645929)
  ·
    refine ⟨5047880935101428490484447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6730507913468571320645929 5047880935101428490484447)
    ·
      refine ⟨7571821402652142735726671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5047880935101428490484447 7571821402652142735726671)
      ·
        refine ⟨11357732103978214103590007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7571821402652142735726671 11357732103978214103590007)
        ·
          refine ⟨17036598155967321155385011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11357732103978214103590007 17036598155967321155385011)
          ·
            refine ⟨25554897233950981733077517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17036598155967321155385011 25554897233950981733077517)
            ·
              refine ⟨9583086462731618149904069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25554897233950981733077517 9583086462731618149904069)
              ·
                refine ⟨1796828711762178403107013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9583086462731618149904069 1796828711762178403107013)
                ·
                  refine ⟨336905383455408450582565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796828711762178403107013 336905383455408450582565)
                  ·
                    refine ⟨63169759397889084484231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336905383455408450582565 63169759397889084484231)
                    ·
                      rfl

theorem cell23_369068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_369068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369068 prefixEnd_369068 := by exact prefixLift 369068
  have htrace : WordTrace (prefixWord ++ tailWord_369068) baseStart_369068 baseEnd_369068 := by
    simpa [prefixWord, tailWord_369068, baseEnd_369068] using wordTrace_append hprefix tailTrace_369068
  have hstable : (prefixWord ++ tailWord_369068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369068).length < 2 ^ (prefixWord ++ tailWord_369068).sum := by decide
  have hdescent : baseEnd_369068 < baseStart_369068 := by decide
  rcases family_descends (prefixWord ++ tailWord_369068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369071 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_369071 : Nat := 118140960795 + 369071 * 2 ^ 59
def prefixEnd_369071 : Nat := 4983230072969 + 3 ^ 40 * 369071 * 2
def baseEnd_369071 : Nat := 189510818635630741715179

theorem tailTrace_369071 : CollatzResearch.WordTrace tailWord_369071 prefixEnd_369071 189510818635630741715179 := by
  unfold tailWord_369071
  simp only [CollatzResearch.WordTrace]
  refine ⟨13461125245926274153651067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8974083497284182769100711 13461125245926274153651067)
  ·
    refine ⟨20191687868889411230476601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13461125245926274153651067 20191687868889411230476601)
    ·
      refine ⟨15143765901667058422857451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20191687868889411230476601 15143765901667058422857451)
      ·
        refine ⟨22715648852500587634286177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15143765901667058422857451 22715648852500587634286177)
        ·
          refine ⟨17036736639375440725714633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22715648852500587634286177 17036736639375440725714633)
          ·
            refine ⟨12777552479531580544285975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17036736639375440725714633 12777552479531580544285975)
            ·
              refine ⟨19166328719297370816428963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12777552479531580544285975 19166328719297370816428963)
              ·
                refine ⟨28749493078946056224643445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19166328719297370816428963 28749493078946056224643445)
                ·
                  refine ⟨2695264976151192771060323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28749493078946056224643445 2695264976151192771060323)
                  ·
                    refine ⟨4042897464226789156590485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2695264976151192771060323 4042897464226789156590485)
                    ·
                      refine ⟨189510818635630741715179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4042897464226789156590485 189510818635630741715179)
                      ·
                        rfl

theorem cell23_369071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_369071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369071 prefixEnd_369071 := by exact prefixLift 369071
  have htrace : WordTrace (prefixWord ++ tailWord_369071) baseStart_369071 baseEnd_369071 := by
    simpa [prefixWord, tailWord_369071, baseEnd_369071] using wordTrace_append hprefix tailTrace_369071
  have hstable : (prefixWord ++ tailWord_369071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369071).length < 2 ^ (prefixWord ++ tailWord_369071).sum := by decide
  have hdescent : baseEnd_369071 < baseStart_369071 := by decide
  rcases family_descends (prefixWord ++ tailWord_369071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369076 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 6]
def baseStart_369076 : Nat := 118140960795 + 369076 * 2 ^ 59
def prefixEnd_369076 : Nat := 4983230072969 + 3 ^ 40 * 369076 * 2
def baseEnd_369076 : Nat := 21057042893211469128073

theorem tailTrace_369076 : CollatzResearch.WordTrace tailWord_369076 prefixEnd_369076 21057042893211469128073 := by
  unfold tailWord_369076
  simp only [CollatzResearch.WordTrace]
  refine ⟨6730653805454080003791541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8974205073938773338388721 6730653805454080003791541)
  ·
    refine ⟨630998794261320000355457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6730653805454080003791541 630998794261320000355457)
    ·
      refine ⟨473249095695990000266593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630998794261320000355457 473249095695990000266593)
      ·
        refine ⟨354936821771992500199945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473249095695990000266593 354936821771992500199945)
        ·
          refine ⟨266202616328994375149959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354936821771992500199945 266202616328994375149959)
          ·
            refine ⟨399303924493491562724939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266202616328994375149959 399303924493491562724939)
            ·
              refine ⟨598955886740237344087409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399303924493491562724939 598955886740237344087409)
              ·
                refine ⟨449216915055178008065557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598955886740237344087409 449216915055178008065557)
                ·
                  refine ⟨21057042893211469128073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 449216915055178008065557 21057042893211469128073)
                  ·
                    rfl

theorem cell23_369076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_369076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369076 prefixEnd_369076 := by exact prefixLift 369076
  have htrace : WordTrace (prefixWord ++ tailWord_369076) baseStart_369076 baseEnd_369076 := by
    simpa [prefixWord, tailWord_369076, baseEnd_369076] using wordTrace_append hprefix tailTrace_369076
  have hstable : (prefixWord ++ tailWord_369076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369076).length < 2 ^ (prefixWord ++ tailWord_369076).sum := by decide
  have hdescent : baseEnd_369076 < baseStart_369076 := by decide
  rcases family_descends (prefixWord ++ tailWord_369076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369085 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_369085 : Nat := 118140960795 + 369085 * 2 ^ 59
def prefixEnd_369085 : Nat := 4983230072969 + 3 ^ 40 * 369085 * 2
def baseEnd_369085 : Nat := 63172669121597895646705

theorem tailTrace_369085 : CollatzResearch.WordTrace tailWord_369085 prefixEnd_369085 63172669121597895646705 := by
  unfold tailWord_369085
  simp only [CollatzResearch.WordTrace]
  refine ⟨13461635867875554544660709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8974423911917036363107139 13461635867875554544660709)
  ·
    refine ⟨2524056725226666477123883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13461635867875554544660709 2524056725226666477123883)
    ·
      refine ⟨3786085087839999715685825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524056725226666477123883 3786085087839999715685825)
      ·
        refine ⟨2839563815879999786764369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3786085087839999715685825 2839563815879999786764369)
        ·
          refine ⟨2129672861909999840073277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2839563815879999786764369 2129672861909999840073277)
          ·
            refine ⟨798627323216249940027479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2129672861909999840073277 798627323216249940027479)
            ·
              refine ⟨1197940984824374910041219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798627323216249940027479 1197940984824374910041219)
              ·
                refine ⟨1796911477236562365061829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197940984824374910041219 1796911477236562365061829)
                ·
                  refine ⟨336920901981855443449093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796911477236562365061829 336920901981855443449093)
                  ·
                    refine ⟨63172669121597895646705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 336920901981855443449093 63172669121597895646705)
                    ·
                      rfl

theorem cell23_369085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_369085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369085 prefixEnd_369085 := by exact prefixLift 369085
  have htrace : WordTrace (prefixWord ++ tailWord_369085) baseStart_369085 baseEnd_369085 := by
    simpa [prefixWord, tailWord_369085, baseEnd_369085] using wordTrace_append hprefix tailTrace_369085
  have hstable : (prefixWord ++ tailWord_369085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369085).length < 2 ^ (prefixWord ++ tailWord_369085).sum := by decide
  have hdescent : baseEnd_369085 < baseStart_369085 := by decide
  rcases family_descends (prefixWord ++ tailWord_369085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369091 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7]
def baseStart_369091 : Nat := 118140960795 + 369091 * 2 ^ 59
def prefixEnd_369091 : Nat := 4983230072969 + 3 ^ 40 * 369091 * 2
def baseEnd_369091 : Nat := 189521088248720663465087

theorem tailTrace_369091 : CollatzResearch.WordTrace tailWord_369091 prefixEnd_369091 189521088248720663465087 := by
  unfold tailWord_369091
  simp only [CollatzResearch.WordTrace]
  refine ⟨13461854705853817569379127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8974569803902545046252751 13461854705853817569379127)
  ·
    refine ⟨20192782058780726354068691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13461854705853817569379127 20192782058780726354068691)
    ·
      refine ⟨30289173088171089531103037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20192782058780726354068691 30289173088171089531103037)
      ·
        refine ⟨11358439908064158574163639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30289173088171089531103037 11358439908064158574163639)
        ·
          refine ⟨17037659862096237861245459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358439908064158574163639 17037659862096237861245459)
          ·
            refine ⟨25556489793144356791868189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17037659862096237861245459 25556489793144356791868189)
            ·
              refine ⟨9583683672429133796950571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25556489793144356791868189 9583683672429133796950571)
              ·
                refine ⟨14375525508643700695425857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9583683672429133796950571 14375525508643700695425857)
                ·
                  refine ⟨10781644131482775521569393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14375525508643700695425857 10781644131482775521569393)
                  ·
                    refine ⟨8086233098612081641177045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10781644131482775521569393 8086233098612081641177045)
                    ·
                      refine ⟨189521088248720663465087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8086233098612081641177045 189521088248720663465087)
                      ·
                        rfl

theorem cell23_369091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_369091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369091 prefixEnd_369091 := by exact prefixLift 369091
  have htrace : WordTrace (prefixWord ++ tailWord_369091) baseStart_369091 baseEnd_369091 := by
    simpa [prefixWord, tailWord_369091, baseEnd_369091] using wordTrace_append hprefix tailTrace_369091
  have hstable : (prefixWord ++ tailWord_369091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369091).length < 2 ^ (prefixWord ++ tailWord_369091).sum := by decide
  have hdescent : baseEnd_369091 < baseStart_369091 := by decide
  rcases family_descends (prefixWord ++ tailWord_369091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369135 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 5, 3, 2]
def baseStart_369135 : Nat := 118140960795 + 369135 * 2 ^ 59
def prefixEnd_369135 : Nat := 4983230072969 + 3 ^ 40 * 369135 * 2
def baseEnd_369135 : Nat := 189543681397518491314885

theorem tailTrace_369135 : CollatzResearch.WordTrace tailWord_369135 prefixEnd_369135 189543681397518491314885 := by
  unfold tailWord_369135
  simp only [CollatzResearch.WordTrace]
  refine ⟨13463459517694413083980859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8975639678462942055987239 13463459517694413083980859)
  ·
    refine ⟨20195189276541619625971289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13463459517694413083980859 20195189276541619625971289)
    ·
      refine ⟨15146391957406214719478467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20195189276541619625971289 15146391957406214719478467)
      ·
        refine ⟨22719587936109322079217701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15146391957406214719478467 22719587936109322079217701)
        ·
          refine ⟨4259922738020497889853319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22719587936109322079217701 4259922738020497889853319)
          ·
            refine ⟨6389884107030746834779979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4259922738020497889853319 6389884107030746834779979)
            ·
              refine ⟨9584826160546120252169969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389884107030746834779979 9584826160546120252169969)
              ·
                refine ⟨7188619620409590189127477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9584826160546120252169969 7188619620409590189127477)
                ·
                  refine ⟨673933089413399080230701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7188619620409590189127477 673933089413399080230701)
                  ·
                    refine ⟨252724908530024655086513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 673933089413399080230701 252724908530024655086513)
                    ·
                      refine ⟨189543681397518491314885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 252724908530024655086513 189543681397518491314885)
                      ·
                        rfl

theorem cell23_369135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 3, 2].length) (baseStart_369135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369135 prefixEnd_369135 := by exact prefixLift 369135
  have htrace : WordTrace (prefixWord ++ tailWord_369135) baseStart_369135 baseEnd_369135 := by
    simpa [prefixWord, tailWord_369135, baseEnd_369135] using wordTrace_append hprefix tailTrace_369135
  have hstable : (prefixWord ++ tailWord_369135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369135).length < 2 ^ (prefixWord ++ tailWord_369135).sum := by decide
  have hdescent : baseEnd_369135 < baseStart_369135 := by decide
  rcases family_descends (prefixWord ++ tailWord_369135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369142 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_369142 : Nat := 118140960795 + 369142 * 2 ^ 59
def prefixEnd_369142 : Nat := 4983230072969 + 3 ^ 40 * 369142 * 2
def baseEnd_369142 : Nat := 189547275762099963927353

theorem tailTrace_369142 : CollatzResearch.WordTrace tailWord_369142 prefixEnd_369142 189547275762099963927353 := by
  unfold tailWord_369142
  simp only [CollatzResearch.WordTrace]
  refine ⟨841482176791815829967855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8975809885779368852990453 841482176791815829967855)
  ·
    refine ⟨1262223265187723744951783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 841482176791815829967855 1262223265187723744951783)
    ·
      refine ⟨1893334897781585617427675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1262223265187723744951783 1893334897781585617427675)
      ·
        refine ⟨2840002346672378426141513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893334897781585617427675 2840002346672378426141513)
        ·
          refine ⟨2130001760004283819606135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2840002346672378426141513 2130001760004283819606135)
          ·
            refine ⟨3195002640006425729409203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130001760004283819606135 3195002640006425729409203)
            ·
              refine ⟨4792503960009638594113805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3195002640006425729409203 4792503960009638594113805)
              ·
                refine ⟨1797188985003614472792677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4792503960009638594113805 1797188985003614472792677)
                ·
                  refine ⟨336972934688177713648627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797188985003614472792677 336972934688177713648627)
                  ·
                    refine ⟨505459402032266570472941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336972934688177713648627 505459402032266570472941)
                    ·
                      refine ⟨189547275762099963927353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505459402032266570472941 189547275762099963927353)
                      ·
                        rfl

theorem cell23_369142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_369142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369142 prefixEnd_369142 := by exact prefixLift 369142
  have htrace : WordTrace (prefixWord ++ tailWord_369142) baseStart_369142 baseEnd_369142 := by
    simpa [prefixWord, tailWord_369142, baseEnd_369142] using wordTrace_append hprefix tailTrace_369142
  have hstable : (prefixWord ++ tailWord_369142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369142).length < 2 ^ (prefixWord ++ tailWord_369142).sum := by decide
  have hdescent : baseEnd_369142 < baseStart_369142 := by decide
  rcases family_descends (prefixWord ++ tailWord_369142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369148 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_369148 : Nat := 118140960795 + 369148 * 2 ^ 59
def prefixEnd_369148 : Nat := 4983230072969 + 3 ^ 40 * 369148 * 2
def baseEnd_369148 : Nat := 189550356646026940452325

theorem tailTrace_369148 : CollatzResearch.WordTrace tailWord_369148 prefixEnd_369148 189550356646026940452325 := by
  unfold tailWord_369148
  simp only [CollatzResearch.WordTrace]
  refine ⟨6731966833323658152102049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8975955777764877536136065 6731966833323658152102049)
  ·
    refine ⟨5048975124992743614076537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6731966833323658152102049 5048975124992743614076537)
    ·
      refine ⟨3786731343744557710557403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5048975124992743614076537 3786731343744557710557403)
      ·
        refine ⟨5680097015616836565836105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786731343744557710557403 5680097015616836565836105)
        ·
          refine ⟨4260072761712627424377079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5680097015616836565836105 4260072761712627424377079)
          ·
            refine ⟨6390109142568941136565619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260072761712627424377079 6390109142568941136565619)
            ·
              refine ⟨9585163713853411704848429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6390109142568941136565619 9585163713853411704848429)
              ·
                refine ⟨3594436392695029389318161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9585163713853411704848429 3594436392695029389318161)
                ·
                  refine ⟨2695827294521272041988621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3594436392695029389318161 2695827294521272041988621)
                  ·
                    refine ⟨1010935235445477015745733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2695827294521272041988621 1010935235445477015745733)
                    ·
                      refine ⟨189550356646026940452325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1010935235445477015745733 189550356646026940452325)
                      ·
                        rfl

theorem cell23_369148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_369148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369148 prefixEnd_369148 := by exact prefixLift 369148
  have htrace : WordTrace (prefixWord ++ tailWord_369148) baseStart_369148 baseEnd_369148 := by
    simpa [prefixWord, tailWord_369148, baseEnd_369148] using wordTrace_append hprefix tailTrace_369148
  have hstable : (prefixWord ++ tailWord_369148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369148).length < 2 ^ (prefixWord ++ tailWord_369148).sum := by decide
  have hdescent : baseEnd_369148 < baseStart_369148 := by decide
  rcases family_descends (prefixWord ++ tailWord_369148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369159 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_369159 : Nat := 118140960795 + 369159 * 2 ^ 59
def prefixEnd_369159 : Nat := 4983230072969 + 3 ^ 40 * 369159 * 2
def baseEnd_369159 : Nat := 189556004933226397414775

theorem tailTrace_369159 : CollatzResearch.WordTrace tailWord_369159 prefixEnd_369159 189556004933226397414775 := by
  unfold tailWord_369159
  simp only [CollatzResearch.WordTrace]
  refine ⟨13464334869607465182854531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8976223246404976788569687 13464334869607465182854531)
  ·
    refine ⟨20196502304411197774281797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13464334869607465182854531 20196502304411197774281797)
    ·
      refine ⟨3786844182077099582677837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20196502304411197774281797 3786844182077099582677837)
      ·
        refine ⟨1420066568278912343504189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3786844182077099582677837 1420066568278912343504189)
        ·
          refine ⟨532524963104592128814071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1420066568278912343504189 532524963104592128814071)
          ·
            refine ⟨798787444656888193221107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532524963104592128814071 798787444656888193221107)
            ·
              refine ⟨1198181166985332289831661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798787444656888193221107 1198181166985332289831661)
              ·
                refine ⟨449317937619499608686873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198181166985332289831661 449317937619499608686873)
                ·
                  refine ⟨336988453214624706515155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449317937619499608686873 336988453214624706515155)
                  ·
                    refine ⟨505482679821937059772733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336988453214624706515155 505482679821937059772733)
                    ·
                      refine ⟨189556004933226397414775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505482679821937059772733 189556004933226397414775)
                      ·
                        rfl

theorem cell23_369159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_369159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369159 prefixEnd_369159 := by exact prefixLift 369159
  have htrace : WordTrace (prefixWord ++ tailWord_369159) baseStart_369159 baseEnd_369159 := by
    simpa [prefixWord, tailWord_369159, baseEnd_369159] using wordTrace_append hprefix tailTrace_369159
  have hstable : (prefixWord ++ tailWord_369159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369159).length < 2 ^ (prefixWord ++ tailWord_369159).sum := by decide
  have hdescent : baseEnd_369159 < baseStart_369159 := by decide
  rcases family_descends (prefixWord ++ tailWord_369159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369215 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 3]
def baseStart_369215 : Nat := 118140960795 + 369215 * 2 ^ 59
def prefixEnd_369215 : Nat := 4983230072969 + 3 ^ 40 * 369215 * 2
def baseEnd_369215 : Nat := 189584759849878178314517

theorem tailTrace_369215 : CollatzResearch.WordTrace tailWord_369215 prefixEnd_369215 189584759849878178314517 := by
  unfold tailWord_369215
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466377357404586746893099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8977584904936391164595399 13466377357404586746893099)
  ·
    refine ⟨20199566036106880120339649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13466377357404586746893099 20199566036106880120339649)
    ·
      refine ⟨15149674527080160090254737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20199566036106880120339649 15149674527080160090254737)
      ·
        refine ⟨11362255895310120067691053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15149674527080160090254737 11362255895310120067691053)
        ·
          refine ⟨4260845960741295025384145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11362255895310120067691053 4260845960741295025384145)
          ·
            refine ⟨3195634470555971269038109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4260845960741295025384145 3195634470555971269038109)
            ·
              refine ⟨1198362926458489225889291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3195634470555971269038109 1198362926458489225889291)
              ·
                refine ⟨1797544389687733838833937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198362926458489225889291 1797544389687733838833937)
                ·
                  refine ⟨1348158292265800379125453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1797544389687733838833937 1348158292265800379125453)
                  ·
                    refine ⟨505559359599675142172045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1348158292265800379125453 505559359599675142172045)
                    ·
                      refine ⟨189584759849878178314517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505559359599675142172045 189584759849878178314517)
                      ·
                        rfl

theorem cell23_369215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_369215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369215 prefixEnd_369215 := by exact prefixLift 369215
  have htrace : WordTrace (prefixWord ++ tailWord_369215) baseStart_369215 baseEnd_369215 := by
    simpa [prefixWord, tailWord_369215, baseEnd_369215] using wordTrace_append hprefix tailTrace_369215
  have hstable : (prefixWord ++ tailWord_369215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369215).length < 2 ^ (prefixWord ++ tailWord_369215).sum := by decide
  have hdescent : baseEnd_369215 < baseStart_369215 := by decide
  rcases family_descends (prefixWord ++ tailWord_369215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369222 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_369222 : Nat := 118140960795 + 369222 * 2 ^ 59
def prefixEnd_369222 : Nat := 4983230072969 + 3 ^ 40 * 369222 * 2
def baseEnd_369222 : Nat := 21065372690495516769665

theorem tailTrace_369222 : CollatzResearch.WordTrace tailWord_369222 prefixEnd_369222 21065372690495516769665 := by
  unfold tailWord_369222
  simp only [CollatzResearch.WordTrace]
  refine ⟨420832270886850841949935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8977755112252817961598613 420832270886850841949935)
  ·
    refine ⟨631248406330276262924903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 420832270886850841949935 631248406330276262924903)
    ·
      refine ⟨946872609495414394387355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631248406330276262924903 946872609495414394387355)
      ·
        refine ⟨1420308914243121591581033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946872609495414394387355 1420308914243121591581033)
        ·
          refine ⟨1065231685682341193685775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1420308914243121591581033 1065231685682341193685775)
          ·
            refine ⟨1597847528523511790528663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065231685682341193685775 1597847528523511790528663)
            ·
              refine ⟨2396771292785267685792995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1597847528523511790528663 2396771292785267685792995)
              ·
                refine ⟨3595156939177901528689493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2396771292785267685792995 3595156939177901528689493)
                ·
                  refine ⟨21065372690495516769665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3595156939177901528689493 21065372690495516769665)
                  ·
                    rfl

theorem cell23_369222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_369222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369222 prefixEnd_369222 := by exact prefixLift 369222
  have htrace : WordTrace (prefixWord ++ tailWord_369222) baseStart_369222 baseEnd_369222 := by
    simpa [prefixWord, tailWord_369222, baseEnd_369222] using wordTrace_append hprefix tailTrace_369222
  have hstable : (prefixWord ++ tailWord_369222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369222).length < 2 ^ (prefixWord ++ tailWord_369222).sum := by decide
  have hdescent : baseEnd_369222 < baseStart_369222 := by decide
  rcases family_descends (prefixWord ++ tailWord_369222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369250 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_369250 : Nat := 118140960795 + 369250 * 2 ^ 59
def prefixEnd_369250 : Nat := 4983230072969 + 3 ^ 40 * 369250 * 2
def baseEnd_369250 : Nat := 189602731672785541376857

theorem tailTrace_369250 : CollatzResearch.WordTrace tailWord_369250 prefixEnd_369250 189602731672785541376857 := by
  unfold tailWord_369250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366913478069446931104301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8978435941518525149611469 3366913478069446931104301)
  ·
    refine ⟨1262592554276042599164113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3366913478069446931104301 1262592554276042599164113)
    ·
      refine ⟨946944415707031949373085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1262592554276042599164113 946944415707031949373085)
      ·
        refine ⟨355104155890136981014907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 946944415707031949373085 355104155890136981014907)
        ·
          refine ⟨532656233835205471522361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355104155890136981014907 532656233835205471522361)
          ·
            refine ⟨399492175376404103641771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532656233835205471522361 399492175376404103641771)
            ·
              refine ⟨599238263064606155462657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399492175376404103641771 599238263064606155462657)
              ·
                refine ⟨449428697298454616596993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599238263064606155462657 449428697298454616596993)
                ·
                  refine ⟨337071522973840962447745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449428697298454616596993 337071522973840962447745)
                  ·
                    refine ⟨252803642230380721835809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 337071522973840962447745 252803642230380721835809)
                    ·
                      refine ⟨189602731672785541376857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 252803642230380721835809 189602731672785541376857)
                      ·
                        rfl

theorem cell23_369250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_369250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369250 prefixEnd_369250 := by exact prefixLift 369250
  have htrace : WordTrace (prefixWord ++ tailWord_369250) baseStart_369250 baseEnd_369250 := by
    simpa [prefixWord, tailWord_369250, baseEnd_369250] using wordTrace_append hprefix tailTrace_369250
  have hstable : (prefixWord ++ tailWord_369250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369250).length < 2 ^ (prefixWord ++ tailWord_369250).sum := by decide
  have hdescent : baseEnd_369250 < baseStart_369250 := by decide
  rcases family_descends (prefixWord ++ tailWord_369250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369255 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_369255 : Nat := 118140960795 + 369255 * 2 ^ 59
def prefixEnd_369255 : Nat := 4983230072969 + 3 ^ 40 * 369255 * 2
def baseEnd_369255 : Nat := 189605299076058021814333

theorem tailTrace_369255 : CollatzResearch.WordTrace tailWord_369255 prefixEnd_369255 189605299076058021814333 := by
  unfold tailWord_369255
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467836277259673578349219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8978557518173115718899479 13467836277259673578349219)
  ·
    refine ⟨20201754415889510367523829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13467836277259673578349219 20201754415889510367523829)
    ·
      refine ⟨1893914476489641596955359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20201754415889510367523829 1893914476489641596955359)
      ·
        refine ⟨2840871714734462395433039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1893914476489641596955359 2840871714734462395433039)
        ·
          refine ⟨4261307572101693593149559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840871714734462395433039 4261307572101693593149559)
          ·
            refine ⟨6391961358152540389724339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261307572101693593149559 6391961358152540389724339)
            ·
              refine ⟨9587942037228810584586509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391961358152540389724339 9587942037228810584586509)
              ·
                refine ⟨3595478263960803969219941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9587942037228810584586509 3595478263960803969219941)
                ·
                  refine ⟨674152174492650744228739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3595478263960803969219941 674152174492650744228739)
                  ·
                    refine ⟨1011228261738976116343109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 674152174492650744228739 1011228261738976116343109)
                    ·
                      refine ⟨189605299076058021814333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1011228261738976116343109 189605299076058021814333)
                      ·
                        rfl

theorem cell23_369255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_369255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369255 prefixEnd_369255 := by exact prefixLift 369255
  have htrace : WordTrace (prefixWord ++ tailWord_369255) baseStart_369255 baseEnd_369255 := by
    simpa [prefixWord, tailWord_369255, baseEnd_369255] using wordTrace_append hprefix tailTrace_369255
  have hstable : (prefixWord ++ tailWord_369255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369255).length < 2 ^ (prefixWord ++ tailWord_369255).sum := by decide
  have hdescent : baseEnd_369255 < baseStart_369255 := by decide
  rcases family_descends (prefixWord ++ tailWord_369255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369275 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 3]
def baseStart_369275 : Nat := 118140960795 + 369275 * 2 ^ 59
def prefixEnd_369275 : Nat := 4983230072969 + 3 ^ 40 * 369275 * 2
def baseEnd_369275 : Nat := 189615568689147943564241

theorem tailTrace_369275 : CollatzResearch.WordTrace tailWord_369275 prefixEnd_369275 189615568689147943564241 := by
  unfold tailWord_369275
  simp only [CollatzResearch.WordTrace]
  refine ⟨13468565737187216994077279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8979043824791477996051519 13468565737187216994077279)
  ·
    refine ⟨20202848605780825491115919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13468565737187216994077279 20202848605780825491115919)
    ·
      refine ⟨30304272908671238236673879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20202848605780825491115919 30304272908671238236673879)
      ·
        refine ⟨45456409363006857355010819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30304272908671238236673879 45456409363006857355010819)
        ·
          refine ⟨68184614044510286032516229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45456409363006857355010819 68184614044510286032516229)
          ·
            refine ⟨12784615133345678631096793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68184614044510286032516229 12784615133345678631096793)
            ·
              refine ⟨9588461350009258973322595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12784615133345678631096793 9588461350009258973322595)
              ·
                refine ⟨14382692025013888459983893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9588461350009258973322595 14382692025013888459983893)
                ·
                  refine ⟨674188688672526021561745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14382692025013888459983893 674188688672526021561745)
                  ·
                    refine ⟨505641516504394516171309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 674188688672526021561745 505641516504394516171309)
                    ·
                      refine ⟨189615568689147943564241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505641516504394516171309 189615568689147943564241)
                      ·
                        rfl

theorem cell23_369275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 3].length) (baseStart_369275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369275 prefixEnd_369275 := by exact prefixLift 369275
  have htrace : WordTrace (prefixWord ++ tailWord_369275) baseStart_369275 baseEnd_369275 := by
    simpa [prefixWord, tailWord_369275, baseEnd_369275] using wordTrace_append hprefix tailTrace_369275
  have hstable : (prefixWord ++ tailWord_369275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369275).length < 2 ^ (prefixWord ++ tailWord_369275).sum := by decide
  have hdescent : baseEnd_369275 < baseStart_369275 := by decide
  rcases family_descends (prefixWord ++ tailWord_369275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369316 : List Nat := [2, 3, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_369316 : Nat := 118140960795 + 369316 * 2 ^ 59
def prefixEnd_369316 : Nat := 4983230072969 + 3 ^ 40 * 369316 * 2
def baseEnd_369316 : Nat := 63212207131994094383851

theorem tailTrace_369316 : CollatzResearch.WordTrace tailWord_369316 prefixEnd_369316 63212207131994094383851 := by
  unfold tailWord_369316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735030565019340498159901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8980040753359120664213201 6735030565019340498159901)
  ·
    refine ⟨2525636461882252686809963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6735030565019340498159901 2525636461882252686809963)
    ·
      refine ⟨3788454692823379030214945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2525636461882252686809963 3788454692823379030214945)
      ·
        refine ⟨2841341019617534272661209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3788454692823379030214945 2841341019617534272661209)
        ·
          refine ⟨2131005764713150704495907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2841341019617534272661209 2131005764713150704495907)
          ·
            refine ⟨3196508647069726056743861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131005764713150704495907 3196508647069726056743861)
            ·
              refine ⟨299672685662786817819737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3196508647069726056743861 299672685662786817819737)
              ·
                refine ⟨224754514247090113364803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299672685662786817819737 224754514247090113364803)
                ·
                  refine ⟨337131771370635170047205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224754514247090113364803 337131771370635170047205)
                  ·
                    refine ⟨63212207131994094383851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337131771370635170047205 63212207131994094383851)
                    ·
                      rfl

theorem cell23_369316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_369316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369316 prefixEnd_369316 := by exact prefixLift 369316
  have htrace : WordTrace (prefixWord ++ tailWord_369316) baseStart_369316 baseEnd_369316 := by
    simpa [prefixWord, tailWord_369316, baseEnd_369316] using wordTrace_append hprefix tailTrace_369316
  have hstable : (prefixWord ++ tailWord_369316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369316).length < 2 ^ (prefixWord ++ tailWord_369316).sum := by decide
  have hdescent : baseEnd_369316 < baseStart_369316 := by decide
  rcases family_descends (prefixWord ++ tailWord_369316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369329 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 6]
def baseStart_369329 : Nat := 118140960795 + 369329 * 2 ^ 59
def prefixEnd_369329 : Nat := 4983230072969 + 3 ^ 40 * 369329 * 2
def baseEnd_369329 : Nat := 21071477404943414698777

theorem tailTrace_369329 : CollatzResearch.WordTrace tailWord_369329 prefixEnd_369329 21071477404943414698777 := by
  unfold tailWord_369329
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470535278991584216543041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8980356852661056144362027 13470535278991584216543041)
  ·
    refine ⟨10102901459243688162407281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13470535278991584216543041 10102901459243688162407281)
    ·
      refine ⟨7577176094432766121805461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10102901459243688162407281 7577176094432766121805461)
      ·
        refine ⟨355180129426535911959631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7577176094432766121805461 355180129426535911959631)
        ·
          refine ⟨532770194139803867939447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355180129426535911959631 532770194139803867939447)
          ·
            refine ⟨799155291209705801909171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532770194139803867939447 799155291209705801909171)
            ·
              refine ⟨1198732936814558702863757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799155291209705801909171 1198732936814558702863757)
              ·
                refine ⟨449524851305459513573909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198732936814558702863757 449524851305459513573909)
                ·
                  refine ⟨21071477404943414698777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 449524851305459513573909 21071477404943414698777)
                  ·
                    rfl

theorem cell23_369329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 6].length) (baseStart_369329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369329 prefixEnd_369329 := by exact prefixLift 369329
  have htrace : WordTrace (prefixWord ++ tailWord_369329) baseStart_369329 baseEnd_369329 := by
    simpa [prefixWord, tailWord_369329, baseEnd_369329] using wordTrace_append hprefix tailTrace_369329
  have hstable : (prefixWord ++ tailWord_369329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369329).length < 2 ^ (prefixWord ++ tailWord_369329).sum := by decide
  have hdescent : baseEnd_369329 < baseStart_369329 := by decide
  rcases family_descends (prefixWord ++ tailWord_369329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369342 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_369342 : Nat := 118140960795 + 369342 * 2 ^ 59
def prefixEnd_369342 : Nat := 4983230072969 + 3 ^ 40 * 369342 * 2
def baseEnd_369342 : Nat := 63216657297666393808811

theorem tailTrace_369342 : CollatzResearch.WordTrace tailWord_369342 prefixEnd_369342 63216657297666393808811 := by
  unfold tailWord_369342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683876178493060929595785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8980672951962991624510853 1683876178493060929595785)
  ·
    refine ⟨1262907133869795697196839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1683876178493060929595785 1262907133869795697196839)
    ·
      refine ⟨1894360700804693545795259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1262907133869795697196839 1894360700804693545795259)
      ·
        refine ⟨2841541051207040318692889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894360700804693545795259 2841541051207040318692889)
        ·
          refine ⟨2131155788405280239019667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2841541051207040318692889 2131155788405280239019667)
          ·
            refine ⟨3196733682607920358529501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131155788405280239019667 3196733682607920358529501)
            ·
              refine ⟨1198775130977970134448563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3196733682607920358529501 1198775130977970134448563)
              ·
                refine ⟨1798162696466955201672845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198775130977970134448563 1798162696466955201672845)
                ·
                  refine ⟨674311011175108200627317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1798162696466955201672845 674311011175108200627317)
                  ·
                    refine ⟨63216657297666393808811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 674311011175108200627317 63216657297666393808811)
                    ·
                      rfl

theorem cell23_369342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_369342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369342 prefixEnd_369342 := by exact prefixLift 369342
  have htrace : WordTrace (prefixWord ++ tailWord_369342) baseStart_369342 baseEnd_369342 := by
    simpa [prefixWord, tailWord_369342, baseEnd_369342] using wordTrace_append hprefix tailTrace_369342
  have hstable : (prefixWord ++ tailWord_369342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369342).length < 2 ^ (prefixWord ++ tailWord_369342).sum := by decide
  have hdescent : baseEnd_369342 < baseStart_369342 := by decide
  rcases family_descends (prefixWord ++ tailWord_369342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369385 : List Nat := [1, 2, 1, 1, 1, 2, 7, 8]
def baseStart_369385 : Nat := 118140960795 + 369385 * 2 ^ 59
def prefixEnd_369385 : Nat := 4983230072969 + 3 ^ 40 * 369385 * 2
def baseEnd_369385 : Nat := 7024890798560833821805

theorem tailTrace_369385 : CollatzResearch.WordTrace tailWord_369385 prefixEnd_369385 7024890798560833821805 := by
  unfold tailWord_369385
  simp only [CollatzResearch.WordTrace]
  refine ⟨13472577766788705780581609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8981718511192470520387739 13472577766788705780581609)
  ·
    refine ⟨10104433325091529335436207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13472577766788705780581609 10104433325091529335436207)
    ·
      refine ⟨15156649987637294003154311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10104433325091529335436207 15156649987637294003154311)
      ·
        refine ⟨22734974981455941004731467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15156649987637294003154311 22734974981455941004731467)
        ·
          refine ⟨34102462472183911507097201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22734974981455941004731467 34102462472183911507097201)
          ·
            refine ⟨25576846854137933630322901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34102462472183911507097201 25576846854137933630322901)
            ·
              refine ⟨599457348143857819460693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25576846854137933630322901 599457348143857819460693)
              ·
                refine ⟨7024890798560833821805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 599457348143857819460693 7024890798560833821805)
                ·
                  rfl

theorem cell23_369385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 8].length) (baseStart_369385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369385 prefixEnd_369385 := by exact prefixLift 369385
  have htrace : WordTrace (prefixWord ++ tailWord_369385) baseStart_369385 baseEnd_369385 := by
    simpa [prefixWord, tailWord_369385, baseEnd_369385] using wordTrace_append hprefix tailTrace_369385
  have hstable : (prefixWord ++ tailWord_369385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369385).length < 2 ^ (prefixWord ++ tailWord_369385).sum := by decide
  have hdescent : baseEnd_369385 < baseStart_369385 := by decide
  rcases family_descends (prefixWord ++ tailWord_369385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369389 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_369389 : Nat := 118140960795 + 369389 * 2 ^ 59
def prefixEnd_369389 : Nat := 4983230072969 + 3 ^ 40 * 369389 * 2
def baseEnd_369389 : Nat := 63224701827920165846239

theorem tailTrace_369389 : CollatzResearch.WordTrace tailWord_369389 prefixEnd_369389 63224701827920165846239 := by
  unfold tailWord_369389
  simp only [CollatzResearch.WordTrace]
  refine ⟨13472723658774214463727221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8981815772516142975818147 13472723658774214463727221)
  ·
    refine ⟨1263067843010082605974427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13472723658774214463727221 1263067843010082605974427)
    ·
      refine ⟨1894601764515123908961641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1263067843010082605974427 1894601764515123908961641)
      ·
        refine ⟨1420951323386342931721231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1894601764515123908961641 1420951323386342931721231)
        ·
          refine ⟨2131426985079514397581847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420951323386342931721231 2131426985079514397581847)
          ·
            refine ⟨3197140477619271596372771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2131426985079514397581847 3197140477619271596372771)
            ·
              refine ⟨4795710716428907394559157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197140477619271596372771 4795710716428907394559157)
              ·
                refine ⟨449597879665210068239921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4795710716428907394559157 449597879665210068239921)
                ·
                  refine ⟨337198409748907551179941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449597879665210068239921 337198409748907551179941)
                  ·
                    refine ⟨63224701827920165846239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337198409748907551179941 63224701827920165846239)
                    ·
                      rfl

theorem cell23_369389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_369389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369389 prefixEnd_369389 := by exact prefixLift 369389
  have htrace : WordTrace (prefixWord ++ tailWord_369389) baseStart_369389 baseEnd_369389 := by
    simpa [prefixWord, tailWord_369389, baseEnd_369389] using wordTrace_append hprefix tailTrace_369389
  have hstable : (prefixWord ++ tailWord_369389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369389).length < 2 ^ (prefixWord ++ tailWord_369389).sum := by decide
  have hdescent : baseEnd_369389 < baseStart_369389 := by decide
  rcases family_descends (prefixWord ++ tailWord_369389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369392 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4]
def baseStart_369392 : Nat := 118140960795 + 369392 * 2 ^ 59
def prefixEnd_369392 : Nat := 4983230072969 + 3 ^ 40 * 369392 * 2
def baseEnd_369392 : Nat := 189675645925723985801203

theorem tailTrace_369392 : CollatzResearch.WordTrace tailWord_369392 prefixEnd_369392 189675645925723985801203 := by
  unfold tailWord_369392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736416538881672988043215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8981888718508897317390953 6736416538881672988043215)
  ·
    refine ⟨10104624808322509482064823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6736416538881672988043215 10104624808322509482064823)
    ·
      refine ⟨15156937212483764223097235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10104624808322509482064823 15156937212483764223097235)
      ·
        refine ⟨22735405818725646334645853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15156937212483764223097235 22735405818725646334645853)
        ·
          refine ⟨8525777182022117375492195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22735405818725646334645853 8525777182022117375492195)
          ·
            refine ⟨12788665773033176063238293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8525777182022117375492195 12788665773033176063238293)
            ·
              refine ⟨599468708110930127964295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12788665773033176063238293 599468708110930127964295)
              ·
                refine ⟨899203062166395191946443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599468708110930127964295 899203062166395191946443)
                ·
                  refine ⟨1348804593249592787919665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899203062166395191946443 1348804593249592787919665)
                  ·
                    refine ⟨1011603444937194590939749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1348804593249592787919665 1011603444937194590939749)
                    ·
                      refine ⟨189675645925723985801203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1011603444937194590939749 189675645925723985801203)
                      ·
                        rfl

theorem cell23_369392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_369392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369392 prefixEnd_369392 := by exact prefixLift 369392
  have htrace : WordTrace (prefixWord ++ tailWord_369392) baseStart_369392 baseEnd_369392 := by
    simpa [prefixWord, tailWord_369392, baseEnd_369392] using wordTrace_append hprefix tailTrace_369392
  have hstable : (prefixWord ++ tailWord_369392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369392).length < 2 ^ (prefixWord ++ tailWord_369392).sum := by decide
  have hdescent : baseEnd_369392 < baseStart_369392 := by decide
  rcases family_descends (prefixWord ++ tailWord_369392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369416 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_369416 : Nat := 118140960795 + 369416 * 2 ^ 59
def prefixEnd_369416 : Nat := 4983230072969 + 3 ^ 40 * 369416 * 2
def baseEnd_369416 : Nat := 189687969461431891901093

theorem tailTrace_369416 : CollatzResearch.WordTrace tailWord_369416 prefixEnd_369416 189687969461431891901093 := by
  unfold tailWord_369416
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736854214838199037480051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8982472286450932049973401 6736854214838199037480051)
  ·
    refine ⟨10105281322257298556220077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6736854214838199037480051 10105281322257298556220077)
    ·
      refine ⟨3789480495846486958582529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10105281322257298556220077 3789480495846486958582529)
      ·
        refine ⟨2842110371884865218936897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3789480495846486958582529 2842110371884865218936897)
        ·
          refine ⟨2131582778913648914202673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2842110371884865218936897 2131582778913648914202673)
          ·
            refine ⟨1598687084185236685652005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2131582778913648914202673 1598687084185236685652005)
            ·
              refine ⟨299753828284731878559751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1598687084185236685652005 299753828284731878559751)
              ·
                refine ⟨449630742427097817839627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299753828284731878559751 449630742427097817839627)
                ·
                  refine ⟨674446113640646726759441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449630742427097817839627 674446113640646726759441)
                  ·
                    refine ⟨505834585230485045069581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 674446113640646726759441 505834585230485045069581)
                    ·
                      refine ⟨189687969461431891901093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505834585230485045069581 189687969461431891901093)
                      ·
                        rfl

theorem cell23_369416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_369416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369416 prefixEnd_369416 := by exact prefixLift 369416
  have htrace : WordTrace (prefixWord ++ tailWord_369416) baseStart_369416 baseEnd_369416 := by
    simpa [prefixWord, tailWord_369416, baseEnd_369416] using wordTrace_append hprefix tailTrace_369416
  have hstable : (prefixWord ++ tailWord_369416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369416).length < 2 ^ (prefixWord ++ tailWord_369416).sum := by decide
  have hdescent : baseEnd_369416 < baseStart_369416 := by decide
  rcases family_descends (prefixWord ++ tailWord_369416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369429 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_369429 : Nat := 118140960795 + 369429 * 2 ^ 59
def prefixEnd_369429 : Nat := 4983230072969 + 3 ^ 40 * 369429 * 2
def baseEnd_369429 : Nat := 189694644709940341038533

theorem tailTrace_369429 : CollatzResearch.WordTrace tailWord_369429 prefixEnd_369429 189694644709940341038533 := by
  unfold tailWord_369429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13474182578629301295183341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8982788385752867530122227 13474182578629301295183341)
  ·
    refine ⟨5052818466985987985693753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13474182578629301295183341 5052818466985987985693753)
    ·
      refine ⟨3789613850239490989270315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5052818466985987985693753 3789613850239490989270315)
      ·
        refine ⟨5684420775359236483905473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3789613850239490989270315 5684420775359236483905473)
        ·
          refine ⟨4263315581519427362929105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5684420775359236483905473 4263315581519427362929105)
          ·
            refine ⟨3197486686139570522196829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263315581519427362929105 3197486686139570522196829)
            ·
              refine ⟨1199057507302338945823811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3197486686139570522196829 1199057507302338945823811)
              ·
                refine ⟨1798586260953508418735717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1199057507302338945823811 1798586260953508418735717)
                ·
                  refine ⟨337234923928782828512947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1798586260953508418735717 337234923928782828512947)
                  ·
                    refine ⟨505852385893174242769421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 337234923928782828512947 505852385893174242769421)
                    ·
                      refine ⟨189694644709940341038533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 505852385893174242769421 189694644709940341038533)
                      ·
                        rfl

theorem cell23_369429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_369429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369429 prefixEnd_369429 := by exact prefixLift 369429
  have htrace : WordTrace (prefixWord ++ tailWord_369429) baseStart_369429 baseEnd_369429 := by
    simpa [prefixWord, tailWord_369429, baseEnd_369429] using wordTrace_append hprefix tailTrace_369429
  have hstable : (prefixWord ++ tailWord_369429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369429).length < 2 ^ (prefixWord ++ tailWord_369429).sum := by decide
  have hdescent : baseEnd_369429 < baseStart_369429 := by decide
  rcases family_descends (prefixWord ++ tailWord_369429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369453 : List Nat := [1, 5, 3, 2, 1, 2, 2, 7]
def baseStart_369453 : Nat := 118140960795 + 369453 * 2 ^ 59
def prefixEnd_369453 : Nat := 4983230072969 + 3 ^ 40 * 369453 * 2
def baseEnd_369453 : Nat := 7026184009098083227349

theorem tailTrace_369453 : CollatzResearch.WordTrace tailWord_369453 prefixEnd_369453 7026184009098083227349 := by
  unfold tailWord_369453
  simp only [CollatzResearch.WordTrace]
  refine ⟨13475057930542353394057013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8983371953694902262704675 13475057930542353394057013)
  ·
    refine ⟨1263286680988345630692845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13475057930542353394057013 1263286680988345630692845)
    ·
      refine ⟨473732505370629611509817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1263286680988345630692845 473732505370629611509817)
      ·
        refine ⟨355299379027972208632363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473732505370629611509817 355299379027972208632363)
        ·
          refine ⟨532949068541958312948545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355299379027972208632363 532949068541958312948545)
          ·
            refine ⟨399711801406468734711409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532949068541958312948545 399711801406468734711409)
            ·
              refine ⟨299783851054851551033557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399711801406468734711409 299783851054851551033557)
              ·
                refine ⟨7026184009098083227349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 299783851054851551033557 7026184009098083227349)
                ·
                  rfl

theorem cell23_369453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 7].length) (baseStart_369453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369453 prefixEnd_369453 := by exact prefixLift 369453
  have htrace : WordTrace (prefixWord ++ tailWord_369453) baseStart_369453 baseEnd_369453 := by
    simpa [prefixWord, tailWord_369453, baseEnd_369453] using wordTrace_append hprefix tailTrace_369453
  have hstable : (prefixWord ++ tailWord_369453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369453).length < 2 ^ (prefixWord ++ tailWord_369453).sum := by decide
  have hdescent : baseEnd_369453 < baseStart_369453 := by decide
  rcases family_descends (prefixWord ++ tailWord_369453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369482 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_369482 : Nat := 118140960795 + 369482 * 2 ^ 59
def prefixEnd_369482 : Nat := 4983230072969 + 3 ^ 40 * 369482 * 2
def baseEnd_369482 : Nat := 189721859184628633675789

theorem tailTrace_369482 : CollatzResearch.WordTrace tailWord_369482 prefixEnd_369482 189721859184628633675789 := by
  unfold tailWord_369482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369028911859322836715675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8984077098291527564575133 3369028911859322836715675)
  ·
    refine ⟨5053543367788984255073513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369028911859322836715675 5053543367788984255073513)
    ·
      refine ⟨3790157525841738191305135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5053543367788984255073513 3790157525841738191305135)
      ·
        refine ⟨5685236288762607286957703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3790157525841738191305135 5685236288762607286957703)
        ·
          refine ⟨8527854433143910930436555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685236288762607286957703 8527854433143910930436555)
          ·
            refine ⟨12791781649715866395654833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8527854433143910930436555 12791781649715866395654833)
            ·
              refine ⟨9593836237286899796741125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12791781649715866395654833 9593836237286899796741125)
              ·
                refine ⟨1798844294491293711888961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9593836237286899796741125 1798844294491293711888961)
                ·
                  refine ⟨1349133220868470283916721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1798844294491293711888961 1349133220868470283916721)
                  ·
                    refine ⟨1011849915651352712937541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1349133220868470283916721 1011849915651352712937541)
                    ·
                      refine ⟨189721859184628633675789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1011849915651352712937541 189721859184628633675789)
                      ·
                        rfl

theorem cell23_369482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_369482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369482 prefixEnd_369482 := by exact prefixLift 369482
  have htrace : WordTrace (prefixWord ++ tailWord_369482) baseStart_369482 baseEnd_369482 := by
    simpa [prefixWord, tailWord_369482, baseEnd_369482] using wordTrace_append hprefix tailTrace_369482
  have hstable : (prefixWord ++ tailWord_369482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369482).length < 2 ^ (prefixWord ++ tailWord_369482).sum := by decide
  have hdescent : baseEnd_369482 < baseStart_369482 := by decide
  rcases family_descends (prefixWord ++ tailWord_369482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369522 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_369522 : Nat := 118140960795 + 369522 * 2 ^ 59
def prefixEnd_369522 : Nat := 4983230072969 + 3 ^ 40 * 369522 * 2
def baseEnd_369522 : Nat := 63247466136936159058535

theorem tailTrace_369522 : CollatzResearch.WordTrace tailWord_369522 prefixEnd_369522 63247466136936159058535 := by
  unfold tailWord_369522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369393641823094544579705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8985049711528252118879213 3369393641823094544579705)
  ·
    refine ⟨2527045231367320908434779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3369393641823094544579705 2527045231367320908434779)
    ·
      refine ⟨3790567847050981362652169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2527045231367320908434779 3790567847050981362652169)
      ·
        refine ⟨2842925885288236021989127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3790567847050981362652169 2842925885288236021989127)
        ·
          refine ⟨4264388827932354032983691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842925885288236021989127 4264388827932354032983691)
          ·
            refine ⟨6396583241898531049475537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264388827932354032983691 6396583241898531049475537)
            ·
              refine ⟨4797437431423898287106653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6396583241898531049475537 4797437431423898287106653)
              ·
                refine ⟨1799039036783961857664995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4797437431423898287106653 1799039036783961857664995)
                ·
                  refine ⟨2698558555175942786497493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1799039036783961857664995 2698558555175942786497493)
                  ·
                    refine ⟨63247466136936159058535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2698558555175942786497493 63247466136936159058535)
                    ·
                      rfl

theorem cell23_369522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_369522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369522 prefixEnd_369522 := by exact prefixLift 369522
  have htrace : WordTrace (prefixWord ++ tailWord_369522) baseStart_369522 baseEnd_369522 := by
    simpa [prefixWord, tailWord_369522, baseEnd_369522] using wordTrace_append hprefix tailTrace_369522
  have hstable : (prefixWord ++ tailWord_369522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369522).length < 2 ^ (prefixWord ++ tailWord_369522).sum := by decide
  have hdescent : baseEnd_369522 < baseStart_369522 := by decide
  rcases family_descends (prefixWord ++ tailWord_369522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369543 : List Nat := [1, 1, 4, 2, 3, 3, 2, 2, 5]
def baseStart_369543 : Nat := 118140960795 + 369543 * 2 ^ 59
def prefixEnd_369543 : Nat := 4983230072969 + 3 ^ 40 * 369543 * 2
def baseEnd_369543 : Nat := 21083686833839210557001

theorem tailTrace_369543 : CollatzResearch.WordTrace tailWord_369543 prefixEnd_369543 21083686833839210557001 := by
  unfold tailWord_369543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13478340500216298764833283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8985560333477532509888855 13478340500216298764833283)
  ·
    refine ⟨20217510750324448147249925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13478340500216298764833283 20217510750324448147249925)
    ·
      refine ⟨3790783265685834027609361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20217510750324448147249925 3790783265685834027609361)
      ·
        refine ⟨2843087449264375520707021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3790783265685834027609361 2843087449264375520707021)
        ·
          refine ⟨1066157793474140820265133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2843087449264375520707021 1066157793474140820265133)
          ·
            refine ⟨399809172552802807599425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1066157793474140820265133 399809172552802807599425)
            ·
              refine ⟨299856879414602105699569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399809172552802807599425 299856879414602105699569)
              ·
                refine ⟨224892659560951579274677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299856879414602105699569 224892659560951579274677)
                ·
                  refine ⟨21083686833839210557001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224892659560951579274677 21083686833839210557001)
                  ·
                    rfl

theorem cell23_369543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 5].length) (baseStart_369543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369543 prefixEnd_369543 := by exact prefixLift 369543
  have htrace : WordTrace (prefixWord ++ tailWord_369543) baseStart_369543 baseEnd_369543 := by
    simpa [prefixWord, tailWord_369543, baseEnd_369543] using wordTrace_append hprefix tailTrace_369543
  have hstable : (prefixWord ++ tailWord_369543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369543).length < 2 ^ (prefixWord ++ tailWord_369543).sum := by decide
  have hdescent : baseEnd_369543 < baseStart_369543 := by decide
  rcases family_descends (prefixWord ++ tailWord_369543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369546 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_369546 : Nat := 118140960795 + 369546 * 2 ^ 59
def prefixEnd_369546 : Nat := 4983230072969 + 3 ^ 40 * 369546 * 2
def baseEnd_369546 : Nat := 189754721946516383275495

theorem tailTrace_369546 : CollatzResearch.WordTrace tailWord_369546 prefixEnd_369546 189754721946516383275495 := by
  unfold tailWord_369546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369612479801357569298123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8985633279470286851461661 3369612479801357569298123)
  ·
    refine ⟨5054418719702036353947185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369612479801357569298123 5054418719702036353947185)
    ·
      refine ⟨3790814039776527265460389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5054418719702036353947185 3790814039776527265460389)
      ·
        refine ⟨710777632458098862273823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3790814039776527265460389 710777632458098862273823)
        ·
          refine ⟨1066166448687148293410735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710777632458098862273823 1066166448687148293410735)
          ·
            refine ⟨1599249673030722440116103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066166448687148293410735 1599249673030722440116103)
            ·
              refine ⟨2398874509546083660174155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1599249673030722440116103 2398874509546083660174155)
              ·
                refine ⟨3598311764319125490261233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2398874509546083660174155 3598311764319125490261233)
                ·
                  refine ⟨2698733823239344117695925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3598311764319125490261233 2698733823239344117695925)
                  ·
                    refine ⟨253006295928688511033993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2698733823239344117695925 253006295928688511033993)
                    ·
                      refine ⟨189754721946516383275495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 253006295928688511033993 189754721946516383275495)
                      ·
                        rfl

theorem cell23_369546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_369546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369546 prefixEnd_369546 := by exact prefixLift 369546
  have htrace : WordTrace (prefixWord ++ tailWord_369546) baseStart_369546 baseEnd_369546 := by
    simpa [prefixWord, tailWord_369546, baseEnd_369546] using wordTrace_append hprefix tailTrace_369546
  have hstable : (prefixWord ++ tailWord_369546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369546).length < 2 ^ (prefixWord ++ tailWord_369546).sum := by decide
  have hdescent : baseEnd_369546 < baseStart_369546 := by decide
  rcases family_descends (prefixWord ++ tailWord_369546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369637 : List Nat := [1, 3, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_369637 : Nat := 118140960795 + 369637 * 2 ^ 59
def prefixEnd_369637 : Nat := 4983230072969 + 3 ^ 40 * 369637 * 2
def baseEnd_369637 : Nat := 63267149562025175745859

theorem tailTrace_369637 : CollatzResearch.WordTrace tailWord_369637 prefixEnd_369637 63267149562025175745859 := by
  unfold tailWord_369637
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481768961875752818755165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8987845974583835212503443 13481768961875752818755165)
  ·
    refine ⟨5055663360703407307033187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13481768961875752818755165 5055663360703407307033187)
    ·
      refine ⟨7583495041055110960549781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5055663360703407307033187 7583495041055110960549781)
      ·
        refine ⟨355476330049458326275771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7583495041055110960549781 355476330049458326275771)
        ·
          refine ⟨533214495074187489413657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355476330049458326275771 533214495074187489413657)
          ·
            refine ⟨399910871305640617060243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533214495074187489413657 399910871305640617060243)
            ·
              refine ⟨599866306958460925590365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399910871305640617060243 599866306958460925590365)
              ·
                refine ⟨224949865109422847096387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 599866306958460925590365 224949865109422847096387)
                ·
                  refine ⟨337424797664134270644581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224949865109422847096387 337424797664134270644581)
                  ·
                    refine ⟨63267149562025175745859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337424797664134270644581 63267149562025175745859)
                    ·
                      rfl

theorem cell23_369637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_369637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369637 prefixEnd_369637 := by exact prefixLift 369637
  have htrace : WordTrace (prefixWord ++ tailWord_369637) baseStart_369637 baseEnd_369637 := by
    simpa [prefixWord, tailWord_369637, baseEnd_369637] using wordTrace_append hprefix tailTrace_369637
  have hstable : (prefixWord ++ tailWord_369637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369637).length < 2 ^ (prefixWord ++ tailWord_369637).sum := by decide
  have hdescent : baseEnd_369637 < baseStart_369637 := by decide
  rcases family_descends (prefixWord ++ tailWord_369637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369669 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_369669 : Nat := 118140960795 + 369669 * 2 ^ 59
def prefixEnd_369669 : Nat := 4983230072969 + 3 ^ 40 * 369669 * 2
def baseEnd_369669 : Nat := 189817880067019402037429

theorem tailTrace_369669 : CollatzResearch.WordTrace tailWord_369669 prefixEnd_369669 189817880067019402037429 := by
  unfold tailWord_369669
  simp only [CollatzResearch.WordTrace]
  refine ⟨13482936097759822283920061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8988624065173214855946707 13482936097759822283920061)
  ·
    refine ⟨5056101036659933356470023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13482936097759822283920061 5056101036659933356470023)
    ·
      refine ⟨7584151554989900034705035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5056101036659933356470023 7584151554989900034705035)
      ·
        refine ⟨11376227332484850052057553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584151554989900034705035 11376227332484850052057553)
        ·
          refine ⟨8532170499363637539043165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11376227332484850052057553 8532170499363637539043165)
          ·
            refine ⟨3199563937261364077141187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8532170499363637539043165 3199563937261364077141187)
            ·
              refine ⟨4799345905892046115711781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199563937261364077141187 4799345905892046115711781)
              ·
                refine ⟨899877357354758646695959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4799345905892046115711781 899877357354758646695959)
                ·
                  refine ⟨1349816036032137970043939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899877357354758646695959 1349816036032137970043939)
                  ·
                    refine ⟨2024724054048206955065909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349816036032137970043939 2024724054048206955065909)
                    ·
                      refine ⟨189817880067019402037429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2024724054048206955065909 189817880067019402037429)
                      ·
                        rfl

theorem cell23_369669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_369669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369669 prefixEnd_369669 := by exact prefixLift 369669
  have htrace : WordTrace (prefixWord ++ tailWord_369669) baseStart_369669 baseEnd_369669 := by
    simpa [prefixWord, tailWord_369669, baseEnd_369669] using wordTrace_append hprefix tailTrace_369669
  have hstable : (prefixWord ++ tailWord_369669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369669).length < 2 ^ (prefixWord ++ tailWord_369669).sum := by decide
  have hdescent : baseEnd_369669 < baseStart_369669 := by decide
  rcases family_descends (prefixWord ++ tailWord_369669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369700 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_369700 : Nat := 118140960795 + 369700 * 2 ^ 59
def prefixEnd_369700 : Nat := 4983230072969 + 3 ^ 40 * 369700 * 2
def baseEnd_369700 : Nat := 189833797967308780749787

theorem tailTrace_369700 : CollatzResearch.WordTrace tailWord_369700 prefixEnd_369700 189833797967308780749787 := by
  unfold tailWord_369700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742033380323757289149277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8989377840431676385532369 6742033380323757289149277)
  ·
    refine ⟨2528262517621408983430979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6742033380323757289149277 2528262517621408983430979)
    ·
      refine ⟨3792393776432113475146469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528262517621408983430979 3792393776432113475146469)
      ·
        refine ⟨711073833081021276589963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3792393776432113475146469 711073833081021276589963)
        ·
          refine ⟨1066610749621531914884945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711073833081021276589963 1066610749621531914884945)
          ·
            refine ⟨799958062216148936163709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066610749621531914884945 799958062216148936163709)
            ·
              refine ⟨299984273331055851061391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 799958062216148936163709 299984273331055851061391)
              ·
                refine ⟨449976409996583776592087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299984273331055851061391 449976409996583776592087)
                ·
                  refine ⟨674964614994875664888131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449976409996583776592087 674964614994875664888131)
                  ·
                    refine ⟨1012446922492313497332197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 674964614994875664888131 1012446922492313497332197)
                    ·
                      refine ⟨189833797967308780749787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1012446922492313497332197 189833797967308780749787)
                      ·
                        rfl

theorem cell23_369700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_369700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369700 prefixEnd_369700 := by exact prefixLift 369700
  have htrace : WordTrace (prefixWord ++ tailWord_369700) baseStart_369700 baseEnd_369700 := by
    simpa [prefixWord, tailWord_369700, baseEnd_369700] using wordTrace_append hprefix tailTrace_369700
  have hstable : (prefixWord ++ tailWord_369700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369700).length < 2 ^ (prefixWord ++ tailWord_369700).sum := by decide
  have hdescent : baseEnd_369700 < baseStart_369700 := by decide
  rcases family_descends (prefixWord ++ tailWord_369700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369703 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_369703 : Nat := 118140960795 + 369703 * 2 ^ 59
def prefixEnd_369703 : Nat := 4983230072969 + 3 ^ 40 * 369703 * 2
def baseEnd_369703 : Nat := 189835338409272269012273

theorem tailTrace_369703 : CollatzResearch.WordTrace tailWord_369703 prefixEnd_369703 189835338409272269012273 := by
  unfold tailWord_369703
  simp only [CollatzResearch.WordTrace]
  refine ⟨13484176179636646090657763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8989450786424430727105175 13484176179636646090657763)
  ·
    refine ⟨20226264269454969135986645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13484176179636646090657763 20226264269454969135986645)
    ·
      refine ⟨474053068815350839124687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 20226264269454969135986645 474053068815350839124687)
      ·
        refine ⟨711079603223026258687031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474053068815350839124687 711079603223026258687031)
        ·
          refine ⟨1066619404834539388030547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711079603223026258687031 1066619404834539388030547)
          ·
            refine ⟨1599929107251809082045821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066619404834539388030547 1599929107251809082045821)
            ·
              refine ⟨599973415219428405767183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1599929107251809082045821 599973415219428405767183)
              ·
                refine ⟨899960122829142608650775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599973415219428405767183 899960122829142608650775)
                ·
                  refine ⟨1349940184243713912976163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899960122829142608650775 1349940184243713912976163)
                  ·
                    refine ⟨2024910276365570869464245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1349940184243713912976163 2024910276365570869464245)
                    ·
                      refine ⟨189835338409272269012273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2024910276365570869464245 189835338409272269012273)
                      ·
                        rfl

theorem cell23_369703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_369703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369703 prefixEnd_369703 := by exact prefixLift 369703
  have htrace : WordTrace (prefixWord ++ tailWord_369703) baseStart_369703 baseEnd_369703 := by
    simpa [prefixWord, tailWord_369703, baseEnd_369703] using wordTrace_append hprefix tailTrace_369703
  have hstable : (prefixWord ++ tailWord_369703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369703).length < 2 ^ (prefixWord ++ tailWord_369703).sum := by decide
  have hdescent : baseEnd_369703 < baseStart_369703 := by decide
  rcases family_descends (prefixWord ++ tailWord_369703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369706 : List Nat := [3, 1, 4, 1, 4, 10]
def baseStart_369706 : Nat := 118140960795 + 369706 * 2 ^ 59
def prefixEnd_369706 : Nat := 4983230072969 + 3 ^ 40 * 369706 * 2
def baseEnd_369706 : Nat := 781221723667636861213

theorem tailTrace_369706 : CollatzResearch.WordTrace tailWord_369706 prefixEnd_369706 781221723667636861213 := by
  unfold tailWord_369706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371071399656444400754243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8989523732417185068677981 3371071399656444400754243)
  ·
    refine ⟨5056607099484666601131365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371071399656444400754243 5056607099484666601131365)
    ·
      refine ⟨948113831153374987712131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5056607099484666601131365 948113831153374987712131)
      ·
        refine ⟨1422170746730062481568197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948113831153374987712131 1422170746730062481568197)
        ·
          refine ⟨266657015011886715294037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1422170746730062481568197 266657015011886715294037)
          ·
            refine ⟨781221723667636861213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 266657015011886715294037 781221723667636861213)
            ·
              rfl

theorem cell23_369706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 10].length) (baseStart_369706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369706 prefixEnd_369706 := by exact prefixLift 369706
  have htrace : WordTrace (prefixWord ++ tailWord_369706) baseStart_369706 baseEnd_369706 := by
    simpa [prefixWord, tailWord_369706, baseEnd_369706] using wordTrace_append hprefix tailTrace_369706
  have hstable : (prefixWord ++ tailWord_369706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369706).length < 2 ^ (prefixWord ++ tailWord_369706).sum := by decide
  have hdescent : baseEnd_369706 < baseStart_369706 := by decide
  rcases family_descends (prefixWord ++ tailWord_369706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369733 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_369733 : Nat := 118140960795 + 369733 * 2 ^ 59
def prefixEnd_369733 : Nat := 4983230072969 + 3 ^ 40 * 369733 * 2
def baseEnd_369733 : Nat := 189850742828907151637135

theorem tailTrace_369733 : CollatzResearch.WordTrace tailWord_369733 prefixEnd_369733 189850742828907151637135 := by
  unfold tailWord_369733
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485270369527961214249853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8990180246351974142833235 13485270369527961214249853)
  ·
    refine ⟨5056976388572985455343695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13485270369527961214249853 5056976388572985455343695)
    ·
      refine ⟨7585464582859478183015543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5056976388572985455343695 7585464582859478183015543)
      ·
        refine ⟨11378196874289217274523315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7585464582859478183015543 11378196874289217274523315)
        ·
          refine ⟨17067295311433825911784973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11378196874289217274523315 17067295311433825911784973)
          ·
            refine ⟨6400235741787684716919365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17067295311433825911784973 6400235741787684716919365)
            ·
              refine ⟨1200044201585190884422381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6400235741787684716919365 1200044201585190884422381)
              ·
                refine ⟨450016575594446581658393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1200044201585190884422381 450016575594446581658393)
                ·
                  refine ⟨337512431695834936243795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450016575594446581658393 337512431695834936243795)
                  ·
                    refine ⟨506268647543752404365693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 337512431695834936243795 506268647543752404365693)
                    ·
                      refine ⟨189850742828907151637135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 506268647543752404365693 189850742828907151637135)
                      ·
                        rfl

theorem cell23_369733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_369733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369733 prefixEnd_369733 := by exact prefixLift 369733
  have htrace : WordTrace (prefixWord ++ tailWord_369733) baseStart_369733 baseEnd_369733 := by
    simpa [prefixWord, tailWord_369733, baseEnd_369733] using wordTrace_append hprefix tailTrace_369733
  have hstable : (prefixWord ++ tailWord_369733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369733).length < 2 ^ (prefixWord ++ tailWord_369733).sum := by decide
  have hdescent : baseEnd_369733 < baseStart_369733 := by decide
  rcases family_descends (prefixWord ++ tailWord_369733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369749 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_369749 : Nat := 118140960795 + 369749 * 2 ^ 59
def prefixEnd_369749 : Nat := 4983230072969 + 3 ^ 40 * 369749 * 2
def baseEnd_369749 : Nat := 63286319506459696345687

theorem tailTrace_369749 : CollatzResearch.WordTrace tailWord_369749 prefixEnd_369749 63286319506459696345687 := by
  unfold tailWord_369749
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485853937469995946832301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8990569291646663964554867 13485853937469995946832301)
  ·
    refine ⟨5057195226551248480062113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13485853937469995946832301 5057195226551248480062113)
    ·
      refine ⟨3792896419913436360046585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5057195226551248480062113 3792896419913436360046585)
      ·
        refine ⟨2844672314935077270034939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3792896419913436360046585 2844672314935077270034939)
        ·
          refine ⟨4267008472402615905052409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844672314935077270034939 4267008472402615905052409)
          ·
            refine ⟨3200256354301961928789307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267008472402615905052409 3200256354301961928789307)
            ·
              refine ⟨4800384531452942893183961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200256354301961928789307 4800384531452942893183961)
              ·
                refine ⟨3600288398589707169887971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800384531452942893183961 3600288398589707169887971)
                ·
                  refine ⟨5400432597884560754831957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600288398589707169887971 5400432597884560754831957)
                  ·
                    refine ⟨63286319506459696345687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5400432597884560754831957 63286319506459696345687)
                    ·
                      rfl

theorem cell23_369749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_369749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369749 prefixEnd_369749 := by exact prefixLift 369749
  have htrace : WordTrace (prefixWord ++ tailWord_369749) baseStart_369749 baseEnd_369749 := by
    simpa [prefixWord, tailWord_369749, baseEnd_369749] using wordTrace_append hprefix tailTrace_369749
  have hstable : (prefixWord ++ tailWord_369749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369749).length < 2 ^ (prefixWord ++ tailWord_369749).sum := by decide
  have hdescent : baseEnd_369749 < baseStart_369749 := by decide
  rcases family_descends (prefixWord ++ tailWord_369749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369759 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_369759 : Nat := 118140960795 + 369759 * 2 ^ 59
def prefixEnd_369759 : Nat := 4983230072969 + 3 ^ 40 * 369759 * 2
def baseEnd_369759 : Nat := 189864093325924049912015

theorem tailTrace_369759 : CollatzResearch.WordTrace tailWord_369759 prefixEnd_369759 189864093325924049912015 := by
  unfold tailWord_369759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486218667433767654696331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8990812444955845103130887 13486218667433767654696331)
  ·
    refine ⟨20229328001150651482044497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13486218667433767654696331 20229328001150651482044497)
    ·
      refine ⟨15171996000862988611533373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20229328001150651482044497 15171996000862988611533373)
      ·
        refine ⟨5689498500323620729325015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15171996000862988611533373 5689498500323620729325015)
        ·
          refine ⟨8534247750485431093987523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5689498500323620729325015 8534247750485431093987523)
          ·
            refine ⟨12801371625728146640981285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8534247750485431093987523 12801371625728146640981285)
            ·
              refine ⟨2400257179824027495183991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12801371625728146640981285 2400257179824027495183991)
              ·
                refine ⟨3600385769736041242775987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400257179824027495183991 3600385769736041242775987)
                ·
                  refine ⟨5400578654604061864163981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600385769736041242775987 5400578654604061864163981)
                  ·
                    refine ⟨2025216995476523199061493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5400578654604061864163981 2025216995476523199061493)
                    ·
                      refine ⟨189864093325924049912015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2025216995476523199061493 189864093325924049912015)
                      ·
                        rfl

theorem cell23_369759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_369759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369759 prefixEnd_369759 := by exact prefixLift 369759
  have htrace : WordTrace (prefixWord ++ tailWord_369759) baseStart_369759 baseEnd_369759 := by
    simpa [prefixWord, tailWord_369759, baseEnd_369759] using wordTrace_append hprefix tailTrace_369759
  have hstable : (prefixWord ++ tailWord_369759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369759).length < 2 ^ (prefixWord ++ tailWord_369759).sum := by decide
  have hdescent : baseEnd_369759 < baseStart_369759 := by decide
  rcases family_descends (prefixWord ++ tailWord_369759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369796 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 7]
def baseStart_369796 : Nat := 118140960795 + 369796 * 2 ^ 59
def prefixEnd_369796 : Nat := 4983230072969 + 3 ^ 40 * 369796 * 2
def baseEnd_369796 : Nat := 21098121345571156127705

theorem tailTrace_369796 : CollatzResearch.WordTrace tailWord_369796 prefixEnd_369796 21098121345571156127705 := by
  unfold tailWord_369796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743784084149861486896621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8991712112199815315862161 6743784084149861486896621)
  ·
    refine ⟨2528919031556198057586233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6743784084149861486896621 2528919031556198057586233)
    ·
      refine ⟨1896689273667148543189675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2528919031556198057586233 1896689273667148543189675)
      ·
        refine ⟨2845033910500722814784513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896689273667148543189675 2845033910500722814784513)
        ·
          refine ⟨2133775432875542111088385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845033910500722814784513 2133775432875542111088385)
          ·
            refine ⟨1600331574656656583316289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2133775432875542111088385 1600331574656656583316289)
            ·
              refine ⟨1200248680992492437487217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600331574656656583316289 1200248680992492437487217)
              ·
                refine ⟨900186510744369328115413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200248680992492437487217 900186510744369328115413)
                ·
                  refine ⟨21098121345571156127705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 900186510744369328115413 21098121345571156127705)
                  ·
                    rfl

theorem cell23_369796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_369796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369796 prefixEnd_369796 := by exact prefixLift 369796
  have htrace : WordTrace (prefixWord ++ tailWord_369796) baseStart_369796 baseEnd_369796 := by
    simpa [prefixWord, tailWord_369796, baseEnd_369796] using wordTrace_append hprefix tailTrace_369796
  have hstable : (prefixWord ++ tailWord_369796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369796).length < 2 ^ (prefixWord ++ tailWord_369796).sum := by decide
  have hdescent : baseEnd_369796 < baseStart_369796 := by decide
  rcases family_descends (prefixWord ++ tailWord_369796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369860 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_369860 : Nat := 118140960795 + 369860 * 2 ^ 59
def prefixEnd_369860 : Nat := 4983230072969 + 3 ^ 40 * 369860 * 2
def baseEnd_369860 : Nat := 63305318290676051583017

theorem tailTrace_369860 : CollatzResearch.WordTrace tailWord_369860 prefixEnd_369860 63305318290676051583017 := by
  unfold tailWord_369860
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744951220033930952061517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8993268293378574602748689 6744951220033930952061517)
  ·
    refine ⟨2529356707512724107023069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6744951220033930952061517 2529356707512724107023069)
    ·
      refine ⟨948508765317271540133651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2529356707512724107023069 948508765317271540133651)
      ·
        refine ⟨1422763147975907310200477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948508765317271540133651 1422763147975907310200477)
        ·
          refine ⟨533536180490965241325179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1422763147975907310200477 533536180490965241325179)
          ·
            refine ⟨800304270736447861987769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533536180490965241325179 800304270736447861987769)
            ·
              refine ⟨600228203052335896490827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800304270736447861987769 600228203052335896490827)
              ·
                refine ⟨900342304578503844736241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600228203052335896490827 900342304578503844736241)
                ·
                  refine ⟨675256728433877883552181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 900342304578503844736241 675256728433877883552181)
                  ·
                    refine ⟨63305318290676051583017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 675256728433877883552181 63305318290676051583017)
                    ·
                      rfl

theorem cell23_369860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_369860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369860 prefixEnd_369860 := by exact prefixLift 369860
  have htrace : WordTrace (prefixWord ++ tailWord_369860) baseStart_369860 baseEnd_369860 := by
    simpa [prefixWord, tailWord_369860, baseEnd_369860] using wordTrace_append hprefix tailTrace_369860
  have hstable : (prefixWord ++ tailWord_369860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369860).length < 2 ^ (prefixWord ++ tailWord_369860).sum := by decide
  have hdescent : baseEnd_369860 < baseStart_369860 := by decide
  rcases family_descends (prefixWord ++ tailWord_369860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_369970 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_369970 : Nat := 118140960795 + 369970 * 2 ^ 59
def prefixEnd_369970 : Nat := 4983230072969 + 3 ^ 40 * 369970 * 2
def baseEnd_369970 : Nat := 189972437744022724373545

theorem tailTrace_369970 : CollatzResearch.WordTrace tailWord_369970 prefixEnd_369970 189972437744022724373545 := by
  unfold tailWord_369970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373478617417337672656841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8995942979779567127084909 3373478617417337672656841)
  ·
    refine ⟨2530108963063003254492631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3373478617417337672656841 2530108963063003254492631)
    ·
      refine ⟨3795163444594504881738947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530108963063003254492631 3795163444594504881738947)
      ·
        refine ⟨5692745166891757322608421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795163444594504881738947 5692745166891757322608421)
        ·
          refine ⟨1067389718792204497989079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5692745166891757322608421 1067389718792204497989079)
          ·
            refine ⟨1601084578188306746983619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067389718792204497989079 1601084578188306746983619)
            ·
              refine ⟨2401626867282460120475429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601084578188306746983619 2401626867282460120475429)
              ·
                refine ⟨450305037615461272589143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2401626867282460120475429 450305037615461272589143)
                ·
                  refine ⟨675457556423191908883715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450305037615461272589143 675457556423191908883715)
                  ·
                    refine ⟨1013186334634787863325573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 675457556423191908883715 1013186334634787863325573)
                    ·
                      refine ⟨189972437744022724373545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1013186334634787863325573 189972437744022724373545)
                      ·
                        rfl

theorem cell23_369970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_369970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_369970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_369970 prefixEnd_369970 := by exact prefixLift 369970
  have htrace : WordTrace (prefixWord ++ tailWord_369970) baseStart_369970 baseEnd_369970 := by
    simpa [prefixWord, tailWord_369970, baseEnd_369970] using wordTrace_append hprefix tailTrace_369970
  have hstable : (prefixWord ++ tailWord_369970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_369970).length < 2 ^ (prefixWord ++ tailWord_369970).sum := by decide
  have hdescent : baseEnd_369970 < baseStart_369970 := by decide
  rcases family_descends (prefixWord ++ tailWord_369970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370024 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_370024 : Nat := 118140960795 + 370024 * 2 ^ 59
def prefixEnd_370024 : Nat := 4983230072969 + 3 ^ 40 * 370024 * 2
def baseEnd_370024 : Nat := 190000165699365513098297

theorem tailTrace_370024 : CollatzResearch.WordTrace tailWord_370024 prefixEnd_370024 190000165699365513098297 := by
  unfold tailWord_370024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747942005736858956546563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8997256007649145275395417 6747942005736858956546563)
  ·
    refine ⟨10121913008605288434819845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6747942005736858956546563 10121913008605288434819845)
    ·
      refine ⟨1897858689113491581528721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10121913008605288434819845 1897858689113491581528721)
      ·
        refine ⟨1423394016835118686146541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1897858689113491581528721 1423394016835118686146541)
        ·
          refine ⟨533772756313169507304953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1423394016835118686146541 533772756313169507304953)
          ·
            refine ⟨400329567234877130478715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533772756313169507304953 400329567234877130478715)
            ·
              refine ⟨600494350852315695718073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400329567234877130478715 600494350852315695718073)
              ·
                refine ⟨450370763139236771788555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600494350852315695718073 450370763139236771788555)
                ·
                  refine ⟨675556144708855157682833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450370763139236771788555 675556144708855157682833)
                  ·
                    refine ⟨506667108531641368262125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 675556144708855157682833 506667108531641368262125)
                    ·
                      refine ⟨190000165699365513098297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 506667108531641368262125 190000165699365513098297)
                      ·
                        rfl

theorem cell23_370024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_370024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370024 prefixEnd_370024 := by exact prefixLift 370024
  have htrace : WordTrace (prefixWord ++ tailWord_370024) baseStart_370024 baseEnd_370024 := by
    simpa [prefixWord, tailWord_370024, baseEnd_370024] using wordTrace_append hprefix tailTrace_370024
  have hstable : (prefixWord ++ tailWord_370024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370024).length < 2 ^ (prefixWord ++ tailWord_370024).sum := by decide
  have hdescent : baseEnd_370024 < baseStart_370024 := by decide
  rcases family_descends (prefixWord ++ tailWord_370024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370037 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_370037 : Nat := 118140960795 + 370037 * 2 ^ 59
def prefixEnd_370037 : Nat := 4983230072969 + 3 ^ 40 * 370037 * 2
def baseEnd_370037 : Nat := 190006840947873962235737

theorem tailTrace_370037 : CollatzResearch.WordTrace tailWord_370037 prefixEnd_370037 190006840947873962235737 := by
  unfold tailWord_370037
  simp only [CollatzResearch.WordTrace]
  refine ⟨13496358160426621133316365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8997572106951080755544243 13496358160426621133316365)
  ·
    refine ⟨5061134310159982924993637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13496358160426621133316365 5061134310159982924993637)
    ·
      refine ⟨948962683154996798436307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5061134310159982924993637 948962683154996798436307)
      ·
        refine ⟨1423444024732495197654461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948962683154996798436307 1423444024732495197654461)
        ·
          refine ⟨533791509274685699120423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1423444024732495197654461 533791509274685699120423)
          ·
            refine ⟨800687263912028548680635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533791509274685699120423 800687263912028548680635)
            ·
              refine ⟨1201030895868042823020953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800687263912028548680635 1201030895868042823020953)
              ·
                refine ⟨900773171901032117265715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201030895868042823020953 900773171901032117265715)
                ·
                  refine ⟨1351159757851548175898573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900773171901032117265715 1351159757851548175898573)
                  ·
                    refine ⟨506684909194330565961965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1351159757851548175898573 506684909194330565961965)
                    ·
                      refine ⟨190006840947873962235737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 506684909194330565961965 190006840947873962235737)
                      ·
                        rfl

theorem cell23_370037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_370037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370037 prefixEnd_370037 := by exact prefixLift 370037
  have htrace : WordTrace (prefixWord ++ tailWord_370037) baseStart_370037 baseEnd_370037 := by
    simpa [prefixWord, tailWord_370037, baseEnd_370037] using wordTrace_append hprefix tailTrace_370037
  have hstable : (prefixWord ++ tailWord_370037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370037).length < 2 ^ (prefixWord ++ tailWord_370037).sum := by decide
  have hdescent : baseEnd_370037 < baseStart_370037 := by decide
  rcases family_descends (prefixWord ++ tailWord_370037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370060 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 3, 4, 2]
def baseStart_370060 : Nat := 118140960795 + 370060 * 2 ^ 59
def prefixEnd_370060 : Nat := 4983230072969 + 3 ^ 40 * 370060 * 2
def baseEnd_370060 : Nat := 190018651002927372248131

theorem tailTrace_370060 : CollatzResearch.WordTrace tailWord_370060 prefixEnd_370060 190018651002927372248131 := by
  unfold tailWord_370060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748598519671648030701817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8998131359562197374269089 6748598519671648030701817)
  ·
    refine ⟨5061448889753736023026363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6748598519671648030701817 5061448889753736023026363)
    ·
      refine ⟨7592173334630604034539545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5061448889753736023026363 7592173334630604034539545)
      ·
        refine ⟨5694130000972953025904659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7592173334630604034539545 5694130000972953025904659)
        ·
          refine ⟨8541195001459429538856989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694130000972953025904659 8541195001459429538856989)
          ·
            refine ⟨3202948125547286077071371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8541195001459429538856989 3202948125547286077071371)
            ·
              refine ⟨4804422188320929115607057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202948125547286077071371 4804422188320929115607057)
              ·
                refine ⟨3603316641240696836705293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4804422188320929115607057 3603316641240696836705293)
                ·
                  refine ⟨1351243740465261313764485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3603316641240696836705293 1351243740465261313764485)
                  ·
                    refine ⟨253358201337236496330841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351243740465261313764485 253358201337236496330841)
                    ·
                      refine ⟨190018651002927372248131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 253358201337236496330841 190018651002927372248131)
                      ·
                        rfl

theorem cell23_370060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_370060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370060 prefixEnd_370060 := by exact prefixLift 370060
  have htrace : WordTrace (prefixWord ++ tailWord_370060) baseStart_370060 baseEnd_370060 := by
    simpa [prefixWord, tailWord_370060, baseEnd_370060] using wordTrace_append hprefix tailTrace_370060
  have hstable : (prefixWord ++ tailWord_370060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370060).length < 2 ^ (prefixWord ++ tailWord_370060).sum := by decide
  have hdescent : baseEnd_370060 < baseStart_370060 := by decide
  rcases family_descends (prefixWord ++ tailWord_370060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370073 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_370073 : Nat := 118140960795 + 370073 * 2 ^ 59
def prefixEnd_370073 : Nat := 4983230072969 + 3 ^ 40 * 370073 * 2
def baseEnd_370073 : Nat := 190025326251435821385571

theorem tailTrace_370073 : CollatzResearch.WordTrace tailWord_370073 prefixEnd_370073 190025326251435821385571 := by
  unfold tailWord_370073
  simp only [CollatzResearch.WordTrace]
  refine ⟨13497671188296199281626873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8998447458864132854417915 13497671188296199281626873)
  ·
    refine ⟨10123253391222149461220155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13497671188296199281626873 10123253391222149461220155)
    ·
      refine ⟨15184880086833224191830233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10123253391222149461220155 15184880086833224191830233)
      ·
        refine ⟨11388660065124918143872675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15184880086833224191830233 11388660065124918143872675)
        ·
          refine ⟨17082990097687377215809013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11388660065124918143872675 17082990097687377215809013)
          ·
            refine ⟨1601530321658191613982095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17082990097687377215809013 1601530321658191613982095)
            ·
              refine ⟨2402295482487287420973143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601530321658191613982095 2402295482487287420973143)
              ·
                refine ⟨3603443223730931131459715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402295482487287420973143 3603443223730931131459715)
                ·
                  refine ⟨5405164835596396697189573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603443223730931131459715 5405164835596396697189573)
                  ·
                    refine ⟨1013468406674324380723045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5405164835596396697189573 1013468406674324380723045)
                    ·
                      refine ⟨190025326251435821385571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1013468406674324380723045 190025326251435821385571)
                      ·
                        rfl

theorem cell23_370073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_370073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370073 prefixEnd_370073 := by exact prefixLift 370073
  have htrace : WordTrace (prefixWord ++ tailWord_370073) baseStart_370073 baseEnd_370073 := by
    simpa [prefixWord, tailWord_370073, baseEnd_370073] using wordTrace_append hprefix tailTrace_370073
  have hstable : (prefixWord ++ tailWord_370073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370073).length < 2 ^ (prefixWord ++ tailWord_370073).sum := by decide
  have hdescent : baseEnd_370073 < baseStart_370073 := by decide
  rcases family_descends (prefixWord ++ tailWord_370073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370077 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_370077 : Nat := 118140960795 + 370077 * 2 ^ 59
def prefixEnd_370077 : Nat := 4983230072969 + 3 ^ 40 * 370077 * 2
def baseEnd_370077 : Nat := 190027380174053805735553

theorem tailTrace_370077 : CollatzResearch.WordTrace tailWord_370077 prefixEnd_370077 190027380174053805735553 := by
  unfold tailWord_370077
  simp only [CollatzResearch.WordTrace]
  refine ⟨13497817080281707964772485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8998544720187805309848323 13497817080281707964772485)
  ·
    refine ⟨2530840702552820243394841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13497817080281707964772485 2530840702552820243394841)
    ·
      refine ⟨1898130526914615182546131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2530840702552820243394841 1898130526914615182546131)
      ·
        refine ⟨2847195790371922773819197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898130526914615182546131 2847195790371922773819197)
        ·
          refine ⟨1067698421389471040182199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2847195790371922773819197 1067698421389471040182199)
          ·
            refine ⟨1601547632084206560273299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067698421389471040182199 1601547632084206560273299)
            ·
              refine ⟨2402321448126309840409949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601547632084206560273299 2402321448126309840409949)
              ·
                refine ⟨900870543047366190153731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2402321448126309840409949 900870543047366190153731)
                ·
                  refine ⟨1351305814571049285230597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900870543047366190153731 1351305814571049285230597)
                  ·
                    refine ⟨253369840232071740980737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351305814571049285230597 253369840232071740980737)
                    ·
                      refine ⟨190027380174053805735553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 253369840232071740980737 190027380174053805735553)
                      ·
                        rfl

theorem cell23_370077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_370077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370077 prefixEnd_370077 := by exact prefixLift 370077
  have htrace : WordTrace (prefixWord ++ tailWord_370077) baseStart_370077 baseEnd_370077 := by
    simpa [prefixWord, tailWord_370077, baseEnd_370077] using wordTrace_append hprefix tailTrace_370077
  have hstable : (prefixWord ++ tailWord_370077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370077).length < 2 ^ (prefixWord ++ tailWord_370077).sum := by decide
  have hdescent : baseEnd_370077 < baseStart_370077 := by decide
  rcases family_descends (prefixWord ++ tailWord_370077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370083 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 7]
def baseStart_370083 : Nat := 118140960795 + 370083 * 2 ^ 59
def prefixEnd_370083 : Nat := 4983230072969 + 3 ^ 40 * 370083 * 2
def baseEnd_370083 : Nat := 21114495673108975806725

theorem tailTrace_370083 : CollatzResearch.WordTrace tailWord_370083 prefixEnd_370083 21114495673108975806725 := by
  unfold tailWord_370083
  simp only [CollatzResearch.WordTrace]
  refine ⟨13498035918259970989490903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8998690612173313992993935 13498035918259970989490903)
  ·
    refine ⟨20247053877389956484236355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13498035918259970989490903 20247053877389956484236355)
    ·
      refine ⟨30370580816084934726354533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20247053877389956484236355 30370580816084934726354533)
      ·
        refine ⟨5694483903015925261191475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30370580816084934726354533 5694483903015925261191475)
        ·
          refine ⟨8541725854523887891787213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694483903015925261191475 8541725854523887891787213)
          ·
            refine ⟨3203147195446457959420205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8541725854523887891787213 3203147195446457959420205)
            ·
              refine ⟨1201180198292421734782577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3203147195446457959420205 1201180198292421734782577)
              ·
                refine ⟨900885148719316301086933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201180198292421734782577 900885148719316301086933)
                ·
                  refine ⟨21114495673108975806725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 900885148719316301086933 21114495673108975806725)
                  ·
                    rfl

theorem cell23_370083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 7].length) (baseStart_370083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370083 prefixEnd_370083 := by exact prefixLift 370083
  have htrace : WordTrace (prefixWord ++ tailWord_370083) baseStart_370083 baseEnd_370083 := by
    simpa [prefixWord, tailWord_370083, baseEnd_370083] using wordTrace_append hprefix tailTrace_370083
  have hstable : (prefixWord ++ tailWord_370083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370083).length < 2 ^ (prefixWord ++ tailWord_370083).sum := by decide
  have hdescent : baseEnd_370083 < baseStart_370083 := by decide
  rcases family_descends (prefixWord ++ tailWord_370083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370123 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5]
def baseStart_370123 : Nat := 118140960795 + 370123 * 2 ^ 59
def prefixEnd_370123 : Nat := 4983230072969 + 3 ^ 40 * 370123 * 2
def baseEnd_370123 : Nat := 190051000284160625760341

theorem tailTrace_370123 : CollatzResearch.WordTrace tailWord_370123 prefixEnd_370123 190051000284160625760341 := by
  unfold tailWord_370123
  simp only [CollatzResearch.WordTrace]
  refine ⟨13499494838115057820947023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8999663225410038547298015 13499494838115057820947023)
  ·
    refine ⟨20249242257172586731420535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13499494838115057820947023 20249242257172586731420535)
    ·
      refine ⟨30373863385758880097130803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20249242257172586731420535 30373863385758880097130803)
      ·
        refine ⟨45560795078638320145696205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30373863385758880097130803 45560795078638320145696205)
        ·
          refine ⟨17085298154489370054636077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45560795078638320145696205 17085298154489370054636077)
          ·
            refine ⟨6406986807933513770488529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17085298154489370054636077 6406986807933513770488529)
            ·
              refine ⟨4805240105950135327866397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6406986807933513770488529 4805240105950135327866397)
              ·
                refine ⟨1801965039731300747949899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4805240105950135327866397 1801965039731300747949899)
                ·
                  refine ⟨2702947559596951121924849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801965039731300747949899 2702947559596951121924849)
                  ·
                    refine ⟨2027210669697713341443637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702947559596951121924849 2027210669697713341443637)
                    ·
                      refine ⟨190051000284160625760341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2027210669697713341443637 190051000284160625760341)
                      ·
                        rfl

theorem cell23_370123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_370123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370123 prefixEnd_370123 := by exact prefixLift 370123
  have htrace : WordTrace (prefixWord ++ tailWord_370123) baseStart_370123 baseEnd_370123 := by
    simpa [prefixWord, tailWord_370123, baseEnd_370123] using wordTrace_append hprefix tailTrace_370123
  have hstable : (prefixWord ++ tailWord_370123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370123).length < 2 ^ (prefixWord ++ tailWord_370123).sum := by decide
  have hdescent : baseEnd_370123 < baseStart_370123 := by decide
  rcases family_descends (prefixWord ++ tailWord_370123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370143 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 2, 8]
def baseStart_370143 : Nat := 118140960795 + 370143 * 2 ^ 59
def prefixEnd_370143 : Nat := 4983230072969 + 3 ^ 40 * 370143 * 2
def baseEnd_370143 : Nat := 63353756632416849170083

theorem tailTrace_370143 : CollatzResearch.WordTrace tailWord_370143 prefixEnd_370143 63353756632416849170083 := by
  unfold tailWord_370143
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500224298042601236675083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9000149532028400824450055 13500224298042601236675083)
  ·
    refine ⟨20250336447063901855012625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13500224298042601236675083 20250336447063901855012625)
    ·
      refine ⟨15187752335297926391259469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20250336447063901855012625 15187752335297926391259469)
      ·
        refine ⟨5695407125736722396722301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15187752335297926391259469 5695407125736722396722301)
        ·
          refine ⟨2135777672151270898770863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5695407125736722396722301 2135777672151270898770863)
          ·
            refine ⟨3203666508226906348156295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135777672151270898770863 3203666508226906348156295)
            ·
              refine ⟨4805499762340359522234443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203666508226906348156295 4805499762340359522234443)
              ·
                refine ⟨7208249643510539283351665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805499762340359522234443 7208249643510539283351665)
                ·
                  refine ⟨5406187232632904462513749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208249643510539283351665 5406187232632904462513749)
                  ·
                    refine ⟨63353756632416849170083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5406187232632904462513749 63353756632416849170083)
                    ·
                      rfl

theorem cell23_370143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_370143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370143 prefixEnd_370143 := by exact prefixLift 370143
  have htrace : WordTrace (prefixWord ++ tailWord_370143) baseStart_370143 baseEnd_370143 := by
    simpa [prefixWord, tailWord_370143, baseEnd_370143] using wordTrace_append hprefix tailTrace_370143
  have hstable : (prefixWord ++ tailWord_370143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370143).length < 2 ^ (prefixWord ++ tailWord_370143).sum := by decide
  have hdescent : baseEnd_370143 < baseStart_370143 := by decide
  rcases family_descends (prefixWord ++ tailWord_370143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370163 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6]
def baseStart_370163 : Nat := 118140960795 + 370163 * 2 ^ 59
def prefixEnd_370163 : Nat := 4983230072969 + 3 ^ 40 * 370163 * 2
def baseEnd_370163 : Nat := 190071539510340469260157

theorem tailTrace_370163 : CollatzResearch.WordTrace tailWord_370163 prefixEnd_370163 190071539510340469260157 := by
  unfold tailWord_370163
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500953757970144652403143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9000635838646763101602095 13500953757970144652403143)
  ·
    refine ⟨20251430636955216978604715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13500953757970144652403143 20251430636955216978604715)
    ·
      refine ⟨30377145955432825467907073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20251430636955216978604715 30377145955432825467907073)
      ·
        refine ⟨22782859466574619100930305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30377145955432825467907073 22782859466574619100930305)
        ·
          refine ⟨17087144599930964325697729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22782859466574619100930305 17087144599930964325697729)
          ·
            refine ⟨12815358449948223244273297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17087144599930964325697729 12815358449948223244273297)
            ·
              refine ⟨9611518837461167433204973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12815358449948223244273297 9611518837461167433204973)
              ·
                refine ⟨3604319564047937787451865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9611518837461167433204973 3604319564047937787451865)
                ·
                  refine ⟨2703239673035953340588899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604319564047937787451865 2703239673035953340588899)
                  ·
                    refine ⟨4054859509553930010883349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2703239673035953340588899 4054859509553930010883349)
                    ·
                      refine ⟨190071539510340469260157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4054859509553930010883349 190071539510340469260157)
                      ·
                        rfl

theorem cell23_370163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_370163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370163 prefixEnd_370163 := by exact prefixLift 370163
  have htrace : WordTrace (prefixWord ++ tailWord_370163) baseStart_370163 baseEnd_370163 := by
    simpa [prefixWord, tailWord_370163, baseEnd_370163] using wordTrace_append hprefix tailTrace_370163
  have hstable : (prefixWord ++ tailWord_370163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370163).length < 2 ^ (prefixWord ++ tailWord_370163).sum := by decide
  have hdescent : baseEnd_370163 < baseStart_370163 := by decide
  rcases family_descends (prefixWord ++ tailWord_370163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370174 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_370174 : Nat := 118140960795 + 370174 * 2 ^ 59
def prefixEnd_370174 : Nat := 4983230072969 + 3 ^ 40 * 370174 * 2
def baseEnd_370174 : Nat := 190077187797539926222607

theorem tailTrace_370174 : CollatzResearch.WordTrace tailWord_370174 prefixEnd_370174 190077187797539926222607 := by
  unfold tailWord_370174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687669370116286691381697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9000903307286862354035717 1687669370116286691381697)
  ·
    refine ⟨1265752027587215018536273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1687669370116286691381697 1265752027587215018536273)
    ·
      refine ⟨949314020690411263902205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1265752027587215018536273 949314020690411263902205)
      ·
        refine ⟨355992757758904223963327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 949314020690411263902205 355992757758904223963327)
        ·
          refine ⟨533989136638356335944991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355992757758904223963327 533989136638356335944991)
          ·
            refine ⟨800983704957534503917487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533989136638356335944991 800983704957534503917487)
            ·
              refine ⟨1201475557436301755876231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800983704957534503917487 1201475557436301755876231)
              ·
                refine ⟨1802213336154452633814347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1201475557436301755876231 1802213336154452633814347)
                ·
                  refine ⟨2703320004231678950721521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802213336154452633814347 2703320004231678950721521)
                  ·
                    refine ⟨2027490003173759213041141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2703320004231678950721521 2027490003173759213041141)
                    ·
                      refine ⟨190077187797539926222607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2027490003173759213041141 190077187797539926222607)
                      ·
                        rfl

theorem cell23_370174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_370174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370174 prefixEnd_370174 := by exact prefixLift 370174
  have htrace : WordTrace (prefixWord ++ tailWord_370174) baseStart_370174 baseEnd_370174 := by
    simpa [prefixWord, tailWord_370174, baseEnd_370174] using wordTrace_append hprefix tailTrace_370174
  have hstable : (prefixWord ++ tailWord_370174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370174).length < 2 ^ (prefixWord ++ tailWord_370174).sum := by decide
  have hdescent : baseEnd_370174 < baseStart_370174 := by decide
  rcases family_descends (prefixWord ++ tailWord_370174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370257 : List Nat := [1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_370257 : Nat := 118140960795 + 370257 * 2 ^ 59
def prefixEnd_370257 : Nat := 4983230072969 + 3 ^ 40 * 370257 * 2
def baseEnd_370257 : Nat := 190119806691863101484725

theorem tailTrace_370257 : CollatzResearch.WordTrace tailWord_370257 prefixEnd_370257 190119806691863101484725 := by
  unfold tailWord_370257
  simp only [CollatzResearch.WordTrace]
  refine ⟨13504382219629598706325025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9002921479753065804216683 13504382219629598706325025)
  ·
    refine ⟨10128286664722199029743769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13504382219629598706325025 10128286664722199029743769)
    ·
      refine ⟨7596214998541649272307827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10128286664722199029743769 7596214998541649272307827)
      ·
        refine ⟨11394322497812473908461741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7596214998541649272307827 11394322497812473908461741)
        ·
          refine ⟨4272870936679677715673153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11394322497812473908461741 4272870936679677715673153)
          ·
            refine ⟨3204653202509758286754865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272870936679677715673153 3204653202509758286754865)
            ·
              refine ⟨2403489901882318715066149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204653202509758286754865 2403489901882318715066149)
              ·
                refine ⟨450654356602934759074903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2403489901882318715066149 450654356602934759074903)
                ·
                  refine ⟨675981534904402138612355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450654356602934759074903 675981534904402138612355)
                  ·
                    refine ⟨1013972302356603207918533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 675981534904402138612355 1013972302356603207918533)
                    ·
                      refine ⟨190119806691863101484725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1013972302356603207918533 190119806691863101484725)
                      ·
                        rfl

theorem cell23_370257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_370257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370257 prefixEnd_370257 := by exact prefixLift 370257
  have htrace : WordTrace (prefixWord ++ tailWord_370257) baseStart_370257 baseEnd_370257 := by
    simpa [prefixWord, tailWord_370257, baseEnd_370257] using wordTrace_append hprefix tailTrace_370257
  have hstable : (prefixWord ++ tailWord_370257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370257).length < 2 ^ (prefixWord ++ tailWord_370257).sum := by decide
  have hdescent : baseEnd_370257 < baseStart_370257 := by decide
  rcases family_descends (prefixWord ++ tailWord_370257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370268 : List Nat := [2, 2, 4, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_370268 : Nat := 118140960795 + 370268 * 2 ^ 59
def prefixEnd_370268 : Nat := 4983230072969 + 3 ^ 40 * 370268 * 2
def baseEnd_370268 : Nat := 190125454979062558447175

theorem tailTrace_370268 : CollatzResearch.WordTrace tailWord_370268 prefixEnd_370268 190125454979062558447175 := by
  unfold tailWord_370268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752391711294873792487729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9003188948393165056650305 6752391711294873792487729)
  ·
    refine ⟨5064293783471155344365797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6752391711294873792487729 5064293783471155344365797)
    ·
      refine ⟨949555084400841627068587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5064293783471155344365797 949555084400841627068587)
      ·
        refine ⟨1424332626601262440602881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949555084400841627068587 1424332626601262440602881)
        ·
          refine ⟨1068249469950946830452161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424332626601262440602881 1068249469950946830452161)
          ·
            refine ⟨801187102463210122839121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068249469950946830452161 801187102463210122839121)
            ·
              refine ⟨600890326847407592129341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801187102463210122839121 600890326847407592129341)
              ·
                refine ⟨225333872567777847048503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 600890326847407592129341 225333872567777847048503)
                ·
                  refine ⟨338000808851666770572755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225333872567777847048503 338000808851666770572755)
                  ·
                    refine ⟨507001213277500155859133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 338000808851666770572755 507001213277500155859133)
                    ·
                      refine ⟨190125454979062558447175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 507001213277500155859133 190125454979062558447175)
                      ·
                        rfl

theorem cell23_370268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_370268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370268 prefixEnd_370268 := by exact prefixLift 370268
  have htrace : WordTrace (prefixWord ++ tailWord_370268) baseStart_370268 baseEnd_370268 := by
    simpa [prefixWord, tailWord_370268, baseEnd_370268] using wordTrace_append hprefix tailTrace_370268
  have hstable : (prefixWord ++ tailWord_370268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370268).length < 2 ^ (prefixWord ++ tailWord_370268).sum := by decide
  have hdescent : baseEnd_370268 < baseStart_370268 := by decide
  rcases family_descends (prefixWord ++ tailWord_370268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370294 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_370294 : Nat := 118140960795 + 370294 * 2 ^ 59
def prefixEnd_370294 : Nat := 4983230072969 + 3 ^ 40 * 370294 * 2
def baseEnd_370294 : Nat := 190138805476079456722055

theorem tailTrace_370294 : CollatzResearch.WordTrace tailWord_370294 prefixEnd_370294 190138805476079456722055 := by
  unfold tailWord_370294
  simp only [CollatzResearch.WordTrace]
  refine ⟨844108232530972126588871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9003821146997036016947957 844108232530972126588871)
  ·
    refine ⟨1266162348796458189883307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 844108232530972126588871 1266162348796458189883307)
    ·
      refine ⟨1899243523194687284824961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266162348796458189883307 1899243523194687284824961)
      ·
        refine ⟨1424432642396015463618721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1899243523194687284824961 1424432642396015463618721)
        ·
          refine ⟨1068324481797011597714041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424432642396015463618721 1068324481797011597714041)
          ·
            refine ⟨801243361347758698285531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068324481797011597714041 801243361347758698285531)
            ·
              refine ⟨1201865042021638047428297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801243361347758698285531 1201865042021638047428297)
              ·
                refine ⟨901398781516228535571223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201865042021638047428297 901398781516228535571223)
                ·
                  refine ⟨1352098172274342803356835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901398781516228535571223 1352098172274342803356835)
                  ·
                    refine ⟨2028147258411514205035253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1352098172274342803356835 2028147258411514205035253)
                    ·
                      refine ⟨190138805476079456722055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2028147258411514205035253 190138805476079456722055)
                      ·
                        rfl

theorem cell23_370294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_370294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370294 prefixEnd_370294 := by exact prefixLift 370294
  have htrace : WordTrace (prefixWord ++ tailWord_370294) baseStart_370294 baseEnd_370294 := by
    simpa [prefixWord, tailWord_370294, baseEnd_370294] using wordTrace_append hprefix tailTrace_370294
  have hstable : (prefixWord ++ tailWord_370294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370294).length < 2 ^ (prefixWord ++ tailWord_370294).sum := by decide
  have hdescent : baseEnd_370294 < baseStart_370294 := by decide
  rcases family_descends (prefixWord ++ tailWord_370294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370301 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_370301 : Nat := 118140960795 + 370301 * 2 ^ 59
def prefixEnd_370301 : Nat := 4983230072969 + 3 ^ 40 * 370301 * 2
def baseEnd_370301 : Nat := 63380799946886976444841

theorem tailTrace_370301 : CollatzResearch.WordTrace tailWord_370301 prefixEnd_370301 63380799946886976444841 := by
  unfold tailWord_370301
  simp only [CollatzResearch.WordTrace]
  refine ⟨13505987031470194220926757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9003991354313462813951171 13505987031470194220926757)
  ·
    refine ⟨2532372568400661416423767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13505987031470194220926757 2532372568400661416423767)
    ·
      refine ⟨3798558852600992124635651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532372568400661416423767 3798558852600992124635651)
      ·
        refine ⟨5697838278901488186953477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3798558852600992124635651 5697838278901488186953477)
        ·
          refine ⟨1068344677294029035053777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5697838278901488186953477 1068344677294029035053777)
          ·
            refine ⟨801258507970521776290333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068344677294029035053777 801258507970521776290333)
            ·
              refine ⟨300471940488945666108875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 801258507970521776290333 300471940488945666108875)
              ·
                refine ⟨450707910733418499163313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300471940488945666108875 450707910733418499163313)
                ·
                  refine ⟨338030933050063874372485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450707910733418499163313 338030933050063874372485)
                  ·
                    refine ⟨63380799946886976444841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338030933050063874372485 63380799946886976444841)
                    ·
                      rfl

theorem cell23_370301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_370301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370301 prefixEnd_370301 := by exact prefixLift 370301
  have htrace : WordTrace (prefixWord ++ tailWord_370301) baseStart_370301 baseEnd_370301 := by
    simpa [prefixWord, tailWord_370301, baseEnd_370301] using wordTrace_append hprefix tailTrace_370301
  have hstable : (prefixWord ++ tailWord_370301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370301).length < 2 ^ (prefixWord ++ tailWord_370301).sum := by decide
  have hdescent : baseEnd_370301 < baseStart_370301 := by decide
  rcases family_descends (prefixWord ++ tailWord_370301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370314 : List Nat := [3, 1, 2, 3, 2, 3, 2, 7]
def baseStart_370314 : Nat := 118140960795 + 370314 * 2 ^ 59
def prefixEnd_370314 : Nat := 4983230072969 + 3 ^ 40 * 370314 * 2
def baseEnd_370314 : Nat := 7042558336635902906369

theorem tailTrace_370314 : CollatzResearch.WordTrace tailWord_370314 prefixEnd_370314 7042558336635902906369 := by
  unfold tailWord_370314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376615295105774360287499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9004307453615398294099997 3376615295105774360287499)
  ·
    refine ⟨5064922942658661540431249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376615295105774360287499 5064922942658661540431249)
    ·
      refine ⟨3798692206993996155323437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5064922942658661540431249 3798692206993996155323437)
      ·
        refine ⟨1424509577622748558246289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3798692206993996155323437 1424509577622748558246289)
        ·
          refine ⟨1068382183217061418684717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424509577622748558246289 1068382183217061418684717)
          ·
            refine ⟨400643318706398032006769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1068382183217061418684717 400643318706398032006769)
            ·
              refine ⟨300482489029798524005077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400643318706398032006769 300482489029798524005077)
              ·
                refine ⟨7042558336635902906369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 300482489029798524005077 7042558336635902906369)
                ·
                  rfl

theorem cell23_370314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 7].length) (baseStart_370314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370314 prefixEnd_370314 := by exact prefixLift 370314
  have htrace : WordTrace (prefixWord ++ tailWord_370314) baseStart_370314 baseEnd_370314 := by
    simpa [prefixWord, tailWord_370314, baseEnd_370314] using wordTrace_append hprefix tailTrace_370314
  have hstable : (prefixWord ++ tailWord_370314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370314).length < 2 ^ (prefixWord ++ tailWord_370314).sum := by decide
  have hdescent : baseEnd_370314 < baseStart_370314 := by decide
  rcases family_descends (prefixWord ++ tailWord_370314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370360 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_370360 : Nat := 118140960795 + 370360 * 2 ^ 59
def prefixEnd_370360 : Nat := 4983230072969 + 3 ^ 40 * 370360 * 2
def baseEnd_370360 : Nat := 190172695199276198496751

theorem tailTrace_370360 : CollatzResearch.WordTrace tailWord_370360 prefixEnd_370360 190172695199276198496751 := by
  unfold tailWord_370360
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754069469128223648662267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9005425958837631531549689 6754069469128223648662267)
  ·
    refine ⟨10131104203692335472993401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6754069469128223648662267 10131104203692335472993401)
    ·
      refine ⟨7598328152769251604745051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10131104203692335472993401 7598328152769251604745051)
      ·
        refine ⟨11397492229153877407117577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7598328152769251604745051 11397492229153877407117577)
        ·
          refine ⟨8548119171865408055338183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11397492229153877407117577 8548119171865408055338183)
          ·
            refine ⟨12822178757798112083007275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8548119171865408055338183 12822178757798112083007275)
            ·
              refine ⟨19233268136697168124510913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12822178757798112083007275 19233268136697168124510913)
              ·
                refine ⟨14424951102522876093383185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19233268136697168124510913 14424951102522876093383185)
                ·
                  refine ⟨10818713326892157070037389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14424951102522876093383185 10818713326892157070037389)
                  ·
                    refine ⟨4057017497584558901264021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10818713326892157070037389 4057017497584558901264021)
                    ·
                      refine ⟨190172695199276198496751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4057017497584558901264021 190172695199276198496751)
                      ·
                        rfl

theorem cell23_370360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_370360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370360 prefixEnd_370360 := by exact prefixLift 370360
  have htrace : WordTrace (prefixWord ++ tailWord_370360) baseStart_370360 baseEnd_370360 := by
    simpa [prefixWord, tailWord_370360, baseEnd_370360] using wordTrace_append hprefix tailTrace_370360
  have hstable : (prefixWord ++ tailWord_370360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370360).length < 2 ^ (prefixWord ++ tailWord_370360).sum := by decide
  have hdescent : baseEnd_370360 < baseStart_370360 := by decide
  rcases family_descends (prefixWord ++ tailWord_370360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370404 : List Nat := [2, 3, 1, 1, 1, 3, 3, 4, 5]
def baseStart_370404 : Nat := 118140960795 + 370404 * 2 ^ 59
def prefixEnd_370404 : Nat := 4983230072969 + 3 ^ 40 * 370404 * 2
def baseEnd_370404 : Nat := 21132809816452669594061

theorem tailTrace_370404 : CollatzResearch.WordTrace tailWord_370404 prefixEnd_370404 21132809816452669594061 := by
  unfold tailWord_370404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754871875048521405963133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9006495833398028541284177 6754871875048521405963133)
  ·
    refine ⟨2533076953143195527236175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6754871875048521405963133 2533076953143195527236175)
    ·
      refine ⟨3799615429714793290854263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2533076953143195527236175 3799615429714793290854263)
      ·
        refine ⟨5699423144572189936281395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3799615429714793290854263 5699423144572189936281395)
        ·
          refine ⟨8549134716858284904422093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5699423144572189936281395 8549134716858284904422093)
          ·
            refine ⟨3205925518821856839158285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8549134716858284904422093 3205925518821856839158285)
            ·
              refine ⟨1202222069558196314684357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3205925518821856839158285 1202222069558196314684357)
              ·
                refine ⟨225416638042161809003317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1202222069558196314684357 225416638042161809003317)
                ·
                  refine ⟨21132809816452669594061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225416638042161809003317 21132809816452669594061)
                  ·
                    rfl

theorem cell23_370404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_370404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370404 prefixEnd_370404 := by exact prefixLift 370404
  have htrace : WordTrace (prefixWord ++ tailWord_370404) baseStart_370404 baseEnd_370404 := by
    simpa [prefixWord, tailWord_370404, baseEnd_370404] using wordTrace_append hprefix tailTrace_370404
  have hstable : (prefixWord ++ tailWord_370404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370404).length < 2 ^ (prefixWord ++ tailWord_370404).sum := by decide
  have hdescent : baseEnd_370404 < baseStart_370404 := by decide
  rcases family_descends (prefixWord ++ tailWord_370404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370414 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_370414 : Nat := 118140960795 + 370414 * 2 ^ 59
def prefixEnd_370414 : Nat := 4983230072969 + 3 ^ 40 * 370414 * 2
def baseEnd_370414 : Nat := 190200423154618987221503

theorem tailTrace_370414 : CollatzResearch.WordTrace tailWord_370414 prefixEnd_370414 190200423154618987221503 := by
  unfold tailWord_370414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1688763560007601814973787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9006738986707209679860197 1688763560007601814973787)
  ·
    refine ⟨2533145340011402722460681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1688763560007601814973787 2533145340011402722460681)
    ·
      refine ⟨1899859005008552041845511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2533145340011402722460681 1899859005008552041845511)
      ·
        refine ⟨2849788507512828062768267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899859005008552041845511 2849788507512828062768267)
        ·
          refine ⟨4274682761269242094152401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849788507512828062768267 4274682761269242094152401)
          ·
            refine ⟨3206012070951931570614301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274682761269242094152401 3206012070951931570614301)
            ·
              refine ⟨1202254526606974338980363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3206012070951931570614301 1202254526606974338980363)
              ·
                refine ⟨1803381789910461508470545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202254526606974338980363 1803381789910461508470545)
                ·
                  refine ⟨1352536342432846131352909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803381789910461508470545 1352536342432846131352909)
                  ·
                    refine ⟨507201128412317299257341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1352536342432846131352909 507201128412317299257341)
                    ·
                      refine ⟨190200423154618987221503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 507201128412317299257341 190200423154618987221503)
                      ·
                        rfl

theorem cell23_370414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_370414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370414 prefixEnd_370414 := by exact prefixLift 370414
  have htrace : WordTrace (prefixWord ++ tailWord_370414) baseStart_370414 baseEnd_370414 := by
    simpa [prefixWord, tailWord_370414, baseEnd_370414] using wordTrace_append hprefix tailTrace_370414
  have hstable : (prefixWord ++ tailWord_370414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370414).length < 2 ^ (prefixWord ++ tailWord_370414).sum := by decide
  have hdescent : baseEnd_370414 < baseStart_370414 := by decide
  rcases family_descends (prefixWord ++ tailWord_370414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370434 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_370434 : Nat := 118140960795 + 370434 * 2 ^ 59
def prefixEnd_370434 : Nat := 4983230072969 + 3 ^ 40 * 370434 * 2
def baseEnd_370434 : Nat := 63403564255902969657137

theorem tailTrace_370434 : CollatzResearch.WordTrace tailWord_370434 prefixEnd_370434 63403564255902969657137 := by
  unfold tailWord_370434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377709484997089483879589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9007225293325571957012237 3377709484997089483879589)
  ·
    refine ⟨633320528436954278227423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3377709484997089483879589 633320528436954278227423)
    ·
      refine ⟨949980792655431417341135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633320528436954278227423 949980792655431417341135)
      ·
        refine ⟨1424971188983147126011703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949980792655431417341135 1424971188983147126011703)
        ·
          refine ⟨2137456783474720689017555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424971188983147126011703 2137456783474720689017555)
          ·
            refine ⟨3206185175212081033526333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137456783474720689017555 3206185175212081033526333)
            ·
              refine ⟨1202319440704530387572375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3206185175212081033526333 1202319440704530387572375)
              ·
                refine ⟨1803479161056795581358563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202319440704530387572375 1803479161056795581358563)
                ·
                  refine ⟨2705218741585193372037845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803479161056795581358563 2705218741585193372037845)
                  ·
                    refine ⟨63403564255902969657137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2705218741585193372037845 63403564255902969657137)
                    ·
                      rfl

theorem cell23_370434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_370434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370434 prefixEnd_370434 := by exact prefixLift 370434
  have htrace : WordTrace (prefixWord ++ tailWord_370434) baseStart_370434 baseEnd_370434 := by
    simpa [prefixWord, tailWord_370434, baseEnd_370434] using wordTrace_append hprefix tailTrace_370434
  have hstable : (prefixWord ++ tailWord_370434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370434).length < 2 ^ (prefixWord ++ tailWord_370434).sum := by decide
  have hdescent : baseEnd_370434 < baseStart_370434 := by decide
  rcases family_descends (prefixWord ++ tailWord_370434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370494 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_370494 : Nat := 118140960795 + 370494 * 2 ^ 59
def prefixEnd_370494 : Nat := 4983230072969 + 3 ^ 40 * 370494 * 2
def baseEnd_370494 : Nat := 21137944622997630469015

theorem tailTrace_370494 : CollatzResearch.WordTrace tailWord_370494 prefixEnd_370494 21137944622997630469015 := by
  unfold tailWord_370494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689128289971373522837817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9008684213180658788468357 1689128289971373522837817)
  ·
    refine ⟨1266846217478530142128363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1689128289971373522837817 1266846217478530142128363)
    ·
      refine ⟨1900269326217795213192545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266846217478530142128363 1900269326217795213192545)
      ·
        refine ⟨1425201994663346409894409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1900269326217795213192545 1425201994663346409894409)
        ·
          refine ⟨1068901495997509807420807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1425201994663346409894409 1068901495997509807420807)
          ·
            refine ⟨1603352243996264711131211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068901495997509807420807 1603352243996264711131211)
            ·
              refine ⟨2405028365994397066696817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1603352243996264711131211 2405028365994397066696817)
              ·
                refine ⟨1803771274495797800022613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405028365994397066696817 1803771274495797800022613)
                ·
                  refine ⟨21137944622997630469015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1803771274495797800022613 21137944622997630469015)
                  ·
                    rfl

theorem cell23_370494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_370494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370494 prefixEnd_370494 := by exact prefixLift 370494
  have htrace : WordTrace (prefixWord ++ tailWord_370494) baseStart_370494 baseEnd_370494 := by
    simpa [prefixWord, tailWord_370494, baseEnd_370494] using wordTrace_append hprefix tailTrace_370494
  have hstable : (prefixWord ++ tailWord_370494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370494).length < 2 ^ (prefixWord ++ tailWord_370494).sum := by decide
  have hdescent : baseEnd_370494 < baseStart_370494 := by decide
  rcases family_descends (prefixWord ++ tailWord_370494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370537 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 5, 6]
def baseStart_370537 : Nat := 118140960795 + 370537 * 2 ^ 59
def prefixEnd_370537 : Nat := 4983230072969 + 3 ^ 40 * 370537 * 2
def baseEnd_370537 : Nat := 63421193758374001994479

theorem tailTrace_370537 : CollatzResearch.WordTrace tailWord_370537 prefixEnd_370537 63421193758374001994479 := by
  unfold tailWord_370537
  simp only [CollatzResearch.WordTrace]
  refine ⟨13514594658615206526517865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9009729772410137684345243 13514594658615206526517865)
  ·
    refine ⟨10135945993961404894888399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13514594658615206526517865 10135945993961404894888399)
    ·
      refine ⟨15203918990942107342332599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10135945993961404894888399 15203918990942107342332599)
      ·
        refine ⟨22805878486413161013498899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15203918990942107342332599 22805878486413161013498899)
        ·
          refine ⟨34208817729619741520248349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22805878486413161013498899 34208817729619741520248349)
          ·
            refine ⟨12828306648607403070093131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34208817729619741520248349 12828306648607403070093131)
            ·
              refine ⟨19242459972911104605139697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12828306648607403070093131 19242459972911104605139697)
              ·
                refine ⟨14431844979683328453854773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19242459972911104605139697 14431844979683328453854773)
                ·
                  refine ⟨1352985466845312042548885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14431844979683328453854773 1352985466845312042548885)
                  ·
                    refine ⟨63421193758374001994479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1352985466845312042548885 63421193758374001994479)
                    ·
                      rfl

theorem cell23_370537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_370537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370537 prefixEnd_370537 := by exact prefixLift 370537
  have htrace : WordTrace (prefixWord ++ tailWord_370537) baseStart_370537 baseEnd_370537 := by
    simpa [prefixWord, tailWord_370537, baseEnd_370537] using wordTrace_append hprefix tailTrace_370537
  have hstable : (prefixWord ++ tailWord_370537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370537).length < 2 ^ (prefixWord ++ tailWord_370537).sum := by decide
  have hdescent : baseEnd_370537 < baseStart_370537 := by decide
  rcases family_descends (prefixWord ++ tailWord_370537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370541 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_370541 : Nat := 118140960795 + 370541 * 2 ^ 59
def prefixEnd_370541 : Nat := 4983230072969 + 3 ^ 40 * 370541 * 2
def baseEnd_370541 : Nat := 63421878399246663444473

theorem tailTrace_370541 : CollatzResearch.WordTrace tailWord_370541 prefixEnd_370541 63421878399246663444473 := by
  unfold tailWord_370541
  simp only [CollatzResearch.WordTrace]
  refine ⟨13514740550600715209663477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9009827033733810139775651 13514740550600715209663477)
  ·
    refine ⟨1267006926618817050905951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13514740550600715209663477 1267006926618817050905951)
    ·
      refine ⟨1900510389928225576358927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267006926618817050905951 1900510389928225576358927)
      ·
        refine ⟨2850765584892338364538391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900510389928225576358927 2850765584892338364538391)
        ·
          refine ⟨4276148377338507546807587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850765584892338364538391 4276148377338507546807587)
          ·
            refine ⟨6414222566007761320211381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276148377338507546807587 6414222566007761320211381)
            ·
              refine ⟨601333365563227623769817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6414222566007761320211381 601333365563227623769817)
              ·
                refine ⟨451000024172420717827363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601333365563227623769817 451000024172420717827363)
                ·
                  refine ⟨676500036258631076741045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451000024172420717827363 676500036258631076741045)
                  ·
                    refine ⟨63421878399246663444473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 676500036258631076741045 63421878399246663444473)
                    ·
                      rfl

theorem cell23_370541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_370541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370541 prefixEnd_370541 := by exact prefixLift 370541
  have htrace : WordTrace (prefixWord ++ tailWord_370541) baseStart_370541 baseEnd_370541 := by
    simpa [prefixWord, tailWord_370541, baseEnd_370541] using wordTrace_append hprefix tailTrace_370541
  have hstable : (prefixWord ++ tailWord_370541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370541).length < 2 ^ (prefixWord ++ tailWord_370541).sum := by decide
  have hdescent : baseEnd_370541 < baseStart_370541 := by decide
  rcases family_descends (prefixWord ++ tailWord_370541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370554 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_370554 : Nat := 118140960795 + 370554 * 2 ^ 59
def prefixEnd_370554 : Nat := 4983230072969 + 3 ^ 40 * 370554 * 2
def baseEnd_370554 : Nat := 63424103482082813156953

theorem tailTrace_370554 : CollatzResearch.WordTrace tailWord_370554 prefixEnd_370554 63424103482082813156953 := by
  unfold tailWord_370554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378803674888404607471679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9010143133035745619924477 3378803674888404607471679)
  ·
    refine ⟨5068205512332606911207519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3378803674888404607471679 5068205512332606911207519)
    ·
      refine ⟨7602308268498910366811279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5068205512332606911207519 7602308268498910366811279)
      ·
        refine ⟨11403462402748365550216919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7602308268498910366811279 11403462402748365550216919)
        ·
          refine ⟨17105193604122548325325379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11403462402748365550216919 17105193604122548325325379)
          ·
            refine ⟨25657790406183822487988069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17105193604122548325325379 25657790406183822487988069)
            ·
              refine ⟨4810835701159466716497763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25657790406183822487988069 4810835701159466716497763)
              ·
                refine ⟨7216253551739200074746645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810835701159466716497763 7216253551739200074746645)
                ·
                  refine ⟨338261885237775003503749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7216253551739200074746645 338261885237775003503749)
                  ·
                    refine ⟨63424103482082813156953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338261885237775003503749 63424103482082813156953)
                    ·
                      rfl

theorem cell23_370554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_370554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370554 prefixEnd_370554 := by exact prefixLift 370554
  have htrace : WordTrace (prefixWord ++ tailWord_370554) baseStart_370554 baseEnd_370554 := by
    simpa [prefixWord, tailWord_370554, baseEnd_370554] using wordTrace_append hprefix tailTrace_370554
  have hstable : (prefixWord ++ tailWord_370554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370554).length < 2 ^ (prefixWord ++ tailWord_370554).sum := by decide
  have hdescent : baseEnd_370554 < baseStart_370554 := by decide
  rcases family_descends (prefixWord ++ tailWord_370554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370567 : List Nat := [1, 1, 4, 2, 15]
def baseStart_370567 : Nat := 118140960795 + 370567 * 2 ^ 59
def prefixEnd_370567 : Nat := 4983230072969 + 3 ^ 40 * 370567 * 2
def baseEnd_370567 : Nat := 261013697798020423331

theorem tailTrace_370567 : CollatzResearch.WordTrace tailWord_370567 prefixEnd_370567 261013697798020423331 := by
  unfold tailWord_370567
  simp only [CollatzResearch.WordTrace]
  refine ⟨13515688848506521650109955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9010459232337681100073303 13515688848506521650109955)
  ·
    refine ⟨20273533272759782475164933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13515688848506521650109955 20273533272759782475164933)
    ·
      refine ⟨3801287488642459214093425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20273533272759782475164933 3801287488642459214093425)
      ·
        refine ⟨2850965616481844410570069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3801287488642459214093425 2850965616481844410570069)
        ·
          refine ⟨261013697798020423331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 2850965616481844410570069 261013697798020423331)
          ·
            rfl

theorem cell23_370567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 15].length) (baseStart_370567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370567 prefixEnd_370567 := by exact prefixLift 370567
  have htrace : WordTrace (prefixWord ++ tailWord_370567) baseStart_370567 baseEnd_370567 := by
    simpa [prefixWord, tailWord_370567, baseEnd_370567] using wordTrace_append hprefix tailTrace_370567
  have hstable : (prefixWord ++ tailWord_370567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370567).length < 2 ^ (prefixWord ++ tailWord_370567).sum := by decide
  have hdescent : baseEnd_370567 < baseStart_370567 := by decide
  rcases family_descends (prefixWord ++ tailWord_370567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370588 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_370588 : Nat := 118140960795 + 370588 * 2 ^ 59
def prefixEnd_370588 : Nat := 4983230072969 + 3 ^ 40 * 370588 * 2
def baseEnd_370588 : Nat := 63429922929500435481901

theorem tailTrace_370588 : CollatzResearch.WordTrace tailWord_370588 prefixEnd_370588 63429922929500435481901 := by
  unfold tailWord_370588
  simp only [CollatzResearch.WordTrace]
  refine ⟨6758227390715221118312209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9010969854286961491082945 6758227390715221118312209)
  ·
    refine ⟨5068670543036415838734157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6758227390715221118312209 5068670543036415838734157)
    ·
      refine ⟨1900751453638655939525309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5068670543036415838734157 1900751453638655939525309)
      ·
        refine ⟨712781795114495977321991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1900751453638655939525309 712781795114495977321991)
        ·
          refine ⟨1069172692671743965982987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712781795114495977321991 1069172692671743965982987)
          ·
            refine ⟨1603759039007615948974481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069172692671743965982987 1603759039007615948974481)
            ·
              refine ⟨1202819279255711961730861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603759039007615948974481 1202819279255711961730861)
              ·
                refine ⟨451057229720891985649073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1202819279255711961730861 451057229720891985649073)
                ·
                  refine ⟨338292922290668989236805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451057229720891985649073 338292922290668989236805)
                  ·
                    refine ⟨63429922929500435481901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338292922290668989236805 63429922929500435481901)
                    ·
                      rfl

theorem cell23_370588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_370588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370588 prefixEnd_370588 := by exact prefixLift 370588
  have htrace : WordTrace (prefixWord ++ tailWord_370588) baseStart_370588 baseEnd_370588 := by
    simpa [prefixWord, tailWord_370588, baseEnd_370588] using wordTrace_append hprefix tailTrace_370588
  have hstable : (prefixWord ++ tailWord_370588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370588).length < 2 ^ (prefixWord ++ tailWord_370588).sum := by decide
  have hdescent : baseEnd_370588 < baseStart_370588 := by decide
  rcases family_descends (prefixWord ++ tailWord_370588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370606 : List Nat := [4, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_370606 : Nat := 118140960795 + 370606 * 2 ^ 59
def prefixEnd_370606 : Nat := 4983230072969 + 3 ^ 40 * 370606 * 2
def baseEnd_370606 : Nat := 190299011440282236020621

theorem tailTrace_370606 : CollatzResearch.WordTrace tailWord_370606 prefixEnd_370606 190299011440282236020621 := by
  unfold tailWord_370606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1689638911920653913847459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9011407530243487540519781 1689638911920653913847459)
  ·
    refine ⟨2534458367880980870771189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1689638911920653913847459 2534458367880980870771189)
    ·
      refine ⟨237605471988841956634799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2534458367880980870771189 237605471988841956634799)
      ·
        refine ⟨356408207983262934952199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237605471988841956634799 356408207983262934952199)
        ·
          refine ⟨534612311974894402428299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356408207983262934952199 534612311974894402428299)
          ·
            refine ⟨801918467962341603642449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534612311974894402428299 801918467962341603642449)
            ·
              refine ⟨601438850971756202731837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801918467962341603642449 601438850971756202731837)
              ·
                refine ⟨225539569114408576024439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601438850971756202731837 225539569114408576024439)
                ·
                  refine ⟨338309353671612864036659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225539569114408576024439 338309353671612864036659)
                  ·
                    refine ⟨507464030507419296054989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 338309353671612864036659 507464030507419296054989)
                    ·
                      refine ⟨190299011440282236020621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 507464030507419296054989 190299011440282236020621)
                      ·
                        rfl

theorem cell23_370606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_370606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370606 prefixEnd_370606 := by exact prefixLift 370606
  have htrace : WordTrace (prefixWord ++ tailWord_370606) baseStart_370606 baseEnd_370606 := by
    simpa [prefixWord, tailWord_370606, baseEnd_370606] using wordTrace_append hprefix tailTrace_370606
  have hstable : (prefixWord ++ tailWord_370606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370606).length < 2 ^ (prefixWord ++ tailWord_370606).sum := by decide
  have hdescent : baseEnd_370606 < baseStart_370606 := by decide
  rcases family_descends (prefixWord ++ tailWord_370606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370611 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 3]
def baseStart_370611 : Nat := 118140960795 + 370611 * 2 ^ 59
def prefixEnd_370611 : Nat := 4983230072969 + 3 ^ 40 * 370611 * 2
def baseEnd_370611 : Nat := 190301578843554716458097

theorem tailTrace_370611 : CollatzResearch.WordTrace tailWord_370611 prefixEnd_370611 190301578843554716458097 := by
  unfold tailWord_370611
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517293660347117164711687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9011529106898078109807791 13517293660347117164711687)
  ·
    refine ⟨20275940490520675747067531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13517293660347117164711687 20275940490520675747067531)
    ·
      refine ⟨30413910735781013620601297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20275940490520675747067531 30413910735781013620601297)
      ·
        refine ⟨22810433051835760215450973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30413910735781013620601297 22810433051835760215450973)
        ·
          refine ⟨8553912394438410080794115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22810433051835760215450973 8553912394438410080794115)
          ·
            refine ⟨12830868591657615121191173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8553912394438410080794115 12830868591657615121191173)
            ·
              refine ⟨2405787860935802835223345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12830868591657615121191173 2405787860935802835223345)
              ·
                refine ⟨1804340895701852126417509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2405787860935802835223345 1804340895701852126417509)
                ·
                  refine ⟨338313917944097273703283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1804340895701852126417509 338313917944097273703283)
                  ·
                    refine ⟨507470876916145910554925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 338313917944097273703283 507470876916145910554925)
                    ·
                      refine ⟨190301578843554716458097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 507470876916145910554925 190301578843554716458097)
                      ·
                        rfl

theorem cell23_370611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 3].length) (baseStart_370611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370611 prefixEnd_370611 := by exact prefixLift 370611
  have htrace : WordTrace (prefixWord ++ tailWord_370611) baseStart_370611 baseEnd_370611 := by
    simpa [prefixWord, tailWord_370611, baseEnd_370611] using wordTrace_append hprefix tailTrace_370611
  have hstable : (prefixWord ++ tailWord_370611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370611).length < 2 ^ (prefixWord ++ tailWord_370611).sum := by decide
  have hdescent : baseEnd_370611 < baseStart_370611 := by decide
  rcases family_descends (prefixWord ++ tailWord_370611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370634 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_370634 : Nat := 118140960795 + 370634 * 2 ^ 59
def prefixEnd_370634 : Nat := 4983230072969 + 3 ^ 40 * 370634 * 2
def baseEnd_370634 : Nat := 190313388898608126470491

theorem tailTrace_370634 : CollatzResearch.WordTrace tailWord_370634 prefixEnd_370634 190313388898608126470491 := by
  unfold tailWord_370634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3379533134815948023199739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9012088359509194728532637 3379533134815948023199739)
  ·
    refine ⟨5069299702223922034799609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3379533134815948023199739 5069299702223922034799609)
    ·
      refine ⟨3801974776667941526099707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5069299702223922034799609 3801974776667941526099707)
      ·
        refine ⟨5702962165001912289149561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3801974776667941526099707 5702962165001912289149561)
        ·
          refine ⟨4277221623751434216862171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5702962165001912289149561 4277221623751434216862171)
          ·
            refine ⟨6415832435627151325293257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277221623751434216862171 6415832435627151325293257)
            ·
              refine ⟨4811874326720363493969943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6415832435627151325293257 4811874326720363493969943)
              ·
                refine ⟨7217811490080545240954915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4811874326720363493969943 7217811490080545240954915)
                ·
                  refine ⟨10826717235120817861432373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7217811490080545240954915 10826717235120817861432373)
                  ·
                    refine ⟨1015004740792576674509285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10826717235120817861432373 1015004740792576674509285)
                    ·
                      refine ⟨190313388898608126470491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1015004740792576674509285 190313388898608126470491)
                      ·
                        rfl

theorem cell23_370634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_370634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370634 prefixEnd_370634 := by exact prefixLift 370634
  have htrace : WordTrace (prefixWord ++ tailWord_370634) baseStart_370634 baseEnd_370634 := by
    simpa [prefixWord, tailWord_370634, baseEnd_370634] using wordTrace_append hprefix tailTrace_370634
  have hstable : (prefixWord ++ tailWord_370634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370634).length < 2 ^ (prefixWord ++ tailWord_370634).sum := by decide
  have hdescent : baseEnd_370634 < baseStart_370634 := by decide
  rcases family_descends (prefixWord ++ tailWord_370634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370652 : List Nat := [2, 2, 6, 1, 1, 2, 2, 7]
def baseStart_370652 : Nat := 118140960795 + 370652 * 2 ^ 59
def prefixEnd_370652 : Nat := 4983230072969 + 3 ^ 40 * 370652 * 2
def baseEnd_370652 : Nat := 7048986353718113186867

theorem tailTrace_370652 : CollatzResearch.WordTrace tailWord_370652 prefixEnd_370652 7048986353718113186867 := by
  unfold tailWord_370652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6759394526599290583477105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9012526035465720777969473 6759394526599290583477105)
  ·
    refine ⟨5069545894949467937607829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6759394526599290583477105 5069545894949467937607829)
    ·
      refine ⟨237634963825756309575367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5069545894949467937607829 237634963825756309575367)
      ·
        refine ⟨356452445738634464363051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237634963825756309575367 356452445738634464363051)
        ·
          refine ⟨534678668607951696544577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356452445738634464363051 534678668607951696544577)
          ·
            refine ⟨401009001455963772408433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534678668607951696544577 401009001455963772408433)
            ·
              refine ⟨300756751091972829306325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 401009001455963772408433 300756751091972829306325)
              ·
                refine ⟨7048986353718113186867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 300756751091972829306325 7048986353718113186867)
                ·
                  rfl

theorem cell23_370652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 7].length) (baseStart_370652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370652 prefixEnd_370652 := by exact prefixLift 370652
  have htrace : WordTrace (prefixWord ++ tailWord_370652) baseStart_370652 baseEnd_370652 := by
    simpa [prefixWord, tailWord_370652, baseEnd_370652] using wordTrace_append hprefix tailTrace_370652
  have hstable : (prefixWord ++ tailWord_370652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370652).length < 2 ^ (prefixWord ++ tailWord_370652).sum := by decide
  have hdescent : baseEnd_370652 < baseStart_370652 := by decide
  rcases family_descends (prefixWord ++ tailWord_370652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370655 : List Nat := [1, 1, 2, 3, 4, 2, 2, 2, 1, 3, 2]
def baseStart_370655 : Nat := 118140960795 + 370655 * 2 ^ 59
def prefixEnd_370655 : Nat := 4983230072969 + 3 ^ 40 * 370655 * 2
def baseEnd_370655 : Nat := 190324171992352544307895

theorem tailTrace_370655 : CollatzResearch.WordTrace tailWord_370655 prefixEnd_370655 190324171992352544307895 := by
  unfold tailWord_370655
  simp only [CollatzResearch.WordTrace]
  refine ⟨13518898472187712679313419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9012598981458475119542279 13518898472187712679313419)
  ·
    refine ⟨20278347708281569018970129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13518898472187712679313419 20278347708281569018970129)
    ·
      refine ⟨15208760781211176764227597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20278347708281569018970129 15208760781211176764227597)
      ·
        refine ⟨5703285292954191286585349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15208760781211176764227597 5703285292954191286585349)
        ·
          refine ⟨1069365992428910866234753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5703285292954191286585349 1069365992428910866234753)
          ·
            refine ⟨802024494321683149676065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1069365992428910866234753 802024494321683149676065)
            ·
              refine ⟨601518370741262362257049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802024494321683149676065 601518370741262362257049)
              ·
                refine ⟨451138778055946771692787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601518370741262362257049 451138778055946771692787)
                ·
                  refine ⟨676708167083920157539181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451138778055946771692787 676708167083920157539181)
                  ·
                    refine ⟨253765562656470059077193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 676708167083920157539181 253765562656470059077193)
                    ·
                      refine ⟨190324171992352544307895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 253765562656470059077193 190324171992352544307895)
                      ·
                        rfl

theorem cell23_370655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_370655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370655 prefixEnd_370655 := by exact prefixLift 370655
  have htrace : WordTrace (prefixWord ++ tailWord_370655) baseStart_370655 baseEnd_370655 := by
    simpa [prefixWord, tailWord_370655, baseEnd_370655] using wordTrace_append hprefix tailTrace_370655
  have hstable : (prefixWord ++ tailWord_370655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370655).length < 2 ^ (prefixWord ++ tailWord_370655).sum := by decide
  have hdescent : baseEnd_370655 < baseStart_370655 := by decide
  rcases family_descends (prefixWord ++ tailWord_370655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370684 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_370684 : Nat := 118140960795 + 370684 * 2 ^ 59
def prefixEnd_370684 : Nat := 4983230072969 + 3 ^ 40 * 370684 * 2
def baseEnd_370684 : Nat := 190339062931332930845261

theorem tailTrace_370684 : CollatzResearch.WordTrace tailWord_370684 prefixEnd_370684 190339062931332930845261 := by
  unfold tailWord_370684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6759978094541325316059553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9013304126055100421412737 6759978094541325316059553)
  ·
    refine ⟨5069983570905993987044665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6759978094541325316059553 5069983570905993987044665)
    ·
      refine ⟨3802487678179495490283499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5069983570905993987044665 3802487678179495490283499)
      ·
        refine ⟨5703731517269243235425249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802487678179495490283499 5703731517269243235425249)
        ·
          refine ⟨4277798637951932426568937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5703731517269243235425249 4277798637951932426568937)
          ·
            refine ⟨3208348978463949319926703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4277798637951932426568937 3208348978463949319926703)
            ·
              refine ⟨4812523467695923979890055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208348978463949319926703 4812523467695923979890055)
              ·
                refine ⟨7218785201543885969835083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4812523467695923979890055 7218785201543885969835083)
                ·
                  refine ⟨10828177802315828954752625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7218785201543885969835083 10828177802315828954752625)
                  ·
                    refine ⟨8121133351736871716064469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10828177802315828954752625 8121133351736871716064469)
                    ·
                      refine ⟨190339062931332930845261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8121133351736871716064469 190339062931332930845261)
                      ·
                        rfl

theorem cell23_370684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_370684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370684 prefixEnd_370684 := by exact prefixLift 370684
  have htrace : WordTrace (prefixWord ++ tailWord_370684) baseStart_370684 baseEnd_370684 := by
    simpa [prefixWord, tailWord_370684, baseEnd_370684] using wordTrace_append hprefix tailTrace_370684
  have hstable : (prefixWord ++ tailWord_370684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370684).length < 2 ^ (prefixWord ++ tailWord_370684).sum := by decide
  have hdescent : baseEnd_370684 < baseStart_370684 := by decide
  rcases family_descends (prefixWord ++ tailWord_370684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370691 : List Nat := [1, 1, 1, 3, 2, 1, 1, 8, 5]
def baseStart_370691 : Nat := 118140960795 + 370691 * 2 ^ 59
def prefixEnd_370691 : Nat := 4983230072969 + 3 ^ 40 * 370691 * 2
def baseEnd_370691 : Nat := 21149184143990489273081

theorem tailTrace_370691 : CollatzResearch.WordTrace tailWord_370691 prefixEnd_370691 21149184143990489273081 := by
  unfold tailWord_370691
  simp only [CollatzResearch.WordTrace]
  refine ⟨13520211500057290827623927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9013474333371527218415951 13520211500057290827623927)
  ·
    refine ⟨20280317250085936241435891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13520211500057290827623927 20280317250085936241435891)
    ·
      refine ⟨30420475875128904362153837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20280317250085936241435891 30420475875128904362153837)
      ·
        refine ⟨11407678453173339135807689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30420475875128904362153837 11407678453173339135807689)
        ·
          refine ⟨8555758839880004351855767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11407678453173339135807689 8555758839880004351855767)
          ·
            refine ⟨12833638259820006527783651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8555758839880004351855767 12833638259820006527783651)
            ·
              refine ⟨19250457389730009791675477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12833638259820006527783651 19250457389730009791675477)
              ·
                refine ⟨225591297535898552246197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19250457389730009791675477 225591297535898552246197)
                ·
                  refine ⟨21149184143990489273081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225591297535898552246197 21149184143990489273081)
                  ·
                    rfl

theorem cell23_370691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 5].length) (baseStart_370691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370691 prefixEnd_370691 := by exact prefixLift 370691
  have htrace : WordTrace (prefixWord ++ tailWord_370691) baseStart_370691 baseEnd_370691 := by
    simpa [prefixWord, tailWord_370691, baseEnd_370691] using wordTrace_append hprefix tailTrace_370691
  have hstable : (prefixWord ++ tailWord_370691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370691).length < 2 ^ (prefixWord ++ tailWord_370691).sum := by decide
  have hdescent : baseEnd_370691 < baseStart_370691 := by decide
  rcases family_descends (prefixWord ++ tailWord_370691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370761 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 3]
def baseStart_370761 : Nat := 118140960795 + 370761 * 2 ^ 59
def prefixEnd_370761 : Nat := 4983230072969 + 3 ^ 40 * 370761 * 2
def baseEnd_370761 : Nat := 190378600941729129582407

theorem tailTrace_370761 : CollatzResearch.WordTrace tailWord_370761 prefixEnd_370761 190378600941729129582407 := by
  unfold tailWord_370761
  simp only [CollatzResearch.WordTrace]
  refine ⟨13522764609803692782672137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9015176406535795188448091 13522764609803692782672137)
  ·
    refine ⟨10142073457352769587004103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13522764609803692782672137 10142073457352769587004103)
    ·
      refine ⟨15213110186029154380506155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142073457352769587004103 15213110186029154380506155)
      ·
        refine ⟨22819665279043731570759233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15213110186029154380506155 22819665279043731570759233)
        ·
          refine ⟨17114748959282798678069425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22819665279043731570759233 17114748959282798678069425)
          ·
            refine ⟨12836061719462099008552069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17114748959282798678069425 12836061719462099008552069)
            ·
              refine ⟨2406761572399143564103513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12836061719462099008552069 2406761572399143564103513)
              ·
                refine ⟨1805071179299357673077635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406761572399143564103513 1805071179299357673077635)
                ·
                  refine ⟨2707606768949036509616453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805071179299357673077635 2707606768949036509616453)
                  ·
                    refine ⟨507676269177944345553085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707606768949036509616453 507676269177944345553085)
                    ·
                      refine ⟨190378600941729129582407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 507676269177944345553085 190378600941729129582407)
                      ·
                        rfl

theorem cell23_370761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_370761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370761 prefixEnd_370761 := by exact prefixLift 370761
  have htrace : WordTrace (prefixWord ++ tailWord_370761) baseStart_370761 baseEnd_370761 := by
    simpa [prefixWord, tailWord_370761, baseEnd_370761] using wordTrace_append hprefix tailTrace_370761
  have hstable : (prefixWord ++ tailWord_370761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370761).length < 2 ^ (prefixWord ++ tailWord_370761).sum := by decide
  have hdescent : baseEnd_370761 < baseStart_370761 := by decide
  rcases family_descends (prefixWord ++ tailWord_370761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370836 : List Nat := [2, 4, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_370836 : Nat := 118140960795 + 370836 * 2 ^ 59
def prefixEnd_370836 : Nat := 4983230072969 + 3 ^ 40 * 370836 * 2
def baseEnd_370836 : Nat := 63472370663605445381521

theorem tailTrace_370836 : CollatzResearch.WordTrace tailWord_370836 prefixEnd_370836 63472370663605445381521 := by
  unfold tailWord_370836
  simp only [CollatzResearch.WordTrace]
  refine ⟨6762750042265990295826181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9017000056354653727768241 6762750042265990295826181)
  ·
    refine ⟨1268015632924873180467409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6762750042265990295826181 1268015632924873180467409)
    ·
      refine ⟨951011724693654885350557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1268015632924873180467409 951011724693654885350557)
      ·
        refine ⟨356629396760120582006459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 951011724693654885350557 356629396760120582006459)
        ·
          refine ⟨534944095140180873009689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356629396760120582006459 534944095140180873009689)
          ·
            refine ⟨401208071355135654757267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534944095140180873009689 401208071355135654757267)
            ·
              refine ⟨601812107032703482135901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401208071355135654757267 601812107032703482135901)
              ·
                refine ⟨225679540137263805800963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601812107032703482135901 225679540137263805800963)
                ·
                  refine ⟨338519310205895708701445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225679540137263805800963 338519310205895708701445)
                  ·
                    refine ⟨63472370663605445381521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338519310205895708701445 63472370663605445381521)
                    ·
                      rfl

theorem cell23_370836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_370836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370836 prefixEnd_370836 := by exact prefixLift 370836
  have htrace : WordTrace (prefixWord ++ tailWord_370836) baseStart_370836 baseEnd_370836 := by
    simpa [prefixWord, tailWord_370836, baseEnd_370836] using wordTrace_append hprefix tailTrace_370836
  have hstable : (prefixWord ++ tailWord_370836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370836).length < 2 ^ (prefixWord ++ tailWord_370836).sum := by decide
  have hdescent : baseEnd_370836 < baseStart_370836 := by decide
  rcases family_descends (prefixWord ++ tailWord_370836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370841 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 1, 6]
def baseStart_370841 : Nat := 118140960795 + 370841 * 2 ^ 59
def prefixEnd_370841 : Nat := 4983230072969 + 3 ^ 40 * 370841 * 2
def baseEnd_370841 : Nat := 63473226464696272194013

theorem tailTrace_370841 : CollatzResearch.WordTrace tailWord_370841 prefixEnd_370841 63473226464696272194013 := by
  unfold tailWord_370841
  simp only [CollatzResearch.WordTrace]
  refine ⟨13525682449513866445584377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9017121633009244297056251 13525682449513866445584377)
  ·
    refine ⟨10144261837135399834188283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13525682449513866445584377 10144261837135399834188283)
    ·
      refine ⟨15216392755703099751282425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10144261837135399834188283 15216392755703099751282425)
      ·
        refine ⟨11412294566777324813461819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15216392755703099751282425 11412294566777324813461819)
        ·
          refine ⟨17118441850165987220192729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11412294566777324813461819 17118441850165987220192729)
          ·
            refine ⟨12838831387624490415144547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17118441850165987220192729 12838831387624490415144547)
            ·
              refine ⟨19258247081436735622716821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12838831387624490415144547 19258247081436735622716821)
              ·
                refine ⟨902730331942346982314851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19258247081436735622716821 902730331942346982314851)
                ·
                  refine ⟨1354095497913520473472277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902730331942346982314851 1354095497913520473472277)
                  ·
                    refine ⟨63473226464696272194013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1354095497913520473472277 63473226464696272194013)
                    ·
                      rfl

theorem cell23_370841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_370841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370841 prefixEnd_370841 := by exact prefixLift 370841
  have htrace : WordTrace (prefixWord ++ tailWord_370841) baseStart_370841 baseEnd_370841 := by
    simpa [prefixWord, tailWord_370841, baseEnd_370841] using wordTrace_append hprefix tailTrace_370841
  have hstable : (prefixWord ++ tailWord_370841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370841).length < 2 ^ (prefixWord ++ tailWord_370841).sum := by decide
  have hdescent : baseEnd_370841 < baseStart_370841 := by decide
  rcases family_descends (prefixWord ++ tailWord_370841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370852 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_370852 : Nat := 118140960795 + 370852 * 2 ^ 59
def prefixEnd_370852 : Nat := 4983230072969 + 3 ^ 40 * 370852 * 2
def baseEnd_370852 : Nat := 190425327681288273544489

theorem tailTrace_370852 : CollatzResearch.WordTrace tailWord_370852 prefixEnd_370852 190425327681288273544489 := by
  unfold tailWord_370852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6763041826237007662117405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9017389101649343549489873 6763041826237007662117405)
  ·
    refine ⟨2536140684838877873294027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6763041826237007662117405 2536140684838877873294027)
    ·
      refine ⟨3804211027258316809941041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536140684838877873294027 3804211027258316809941041)
      ·
        refine ⟨2853158270443737607455781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3804211027258316809941041 2853158270443737607455781)
        ·
          refine ⟨534967175708200801397959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2853158270443737607455781 534967175708200801397959)
          ·
            refine ⟨802450763562301202096939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534967175708200801397959 802450763562301202096939)
            ·
              refine ⟨1203676145343451803145409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802450763562301202096939 1203676145343451803145409)
              ·
                refine ⟨902757109007588852359057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203676145343451803145409 902757109007588852359057)
                ·
                  refine ⟨677067831755691639269293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 902757109007588852359057 677067831755691639269293)
                  ·
                    refine ⟨253900436908384364725985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677067831755691639269293 253900436908384364725985)
                    ·
                      refine ⟨190425327681288273544489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 253900436908384364725985 190425327681288273544489)
                      ·
                        rfl

theorem cell23_370852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_370852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370852 prefixEnd_370852 := by exact prefixLift 370852
  have htrace : WordTrace (prefixWord ++ tailWord_370852) baseStart_370852 baseEnd_370852 := by
    simpa [prefixWord, tailWord_370852, baseEnd_370852] using wordTrace_append hprefix tailTrace_370852
  have hstable : (prefixWord ++ tailWord_370852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370852).length < 2 ^ (prefixWord ++ tailWord_370852).sum := by decide
  have hdescent : baseEnd_370852 < baseStart_370852 := by decide
  rcases family_descends (prefixWord ++ tailWord_370852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370871 : List Nat := [1, 1, 3, 1, 4, 2, 1, 10]
def baseStart_370871 : Nat := 118140960795 + 370871 * 2 ^ 59
def prefixEnd_370871 : Nat := 4983230072969 + 3 ^ 40 * 370871 * 2
def baseEnd_370871 : Nat := 7053151252360137007663

theorem tailTrace_370871 : CollatzResearch.WordTrace tailWord_370871 prefixEnd_370871 7053151252360137007663 := by
  unfold tailWord_370871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13526776639405181569176467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9017851092936787712784311 13526776639405181569176467)
  ·
    refine ⟨20290164959107772353764701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13526776639405181569176467 20290164959107772353764701)
    ·
      refine ⟨7608811859665414632661763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20290164959107772353764701 7608811859665414632661763)
      ·
        refine ⟨11413217789498121948992645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7608811859665414632661763 11413217789498121948992645)
        ·
          refine ⟨2139978335530897865436121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11413217789498121948992645 2139978335530897865436121)
          ·
            refine ⟨1604983751648173399077091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2139978335530897865436121 1604983751648173399077091)
            ·
              refine ⟨2407475627472260098615637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604983751648173399077091 2407475627472260098615637)
              ·
                refine ⟨7053151252360137007663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2407475627472260098615637 7053151252360137007663)
                ·
                  rfl

theorem cell23_370871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 10].length) (baseStart_370871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370871 prefixEnd_370871 := by exact prefixLift 370871
  have htrace : WordTrace (prefixWord ++ tailWord_370871) baseStart_370871 baseEnd_370871 := by
    simpa [prefixWord, tailWord_370871, baseEnd_370871] using wordTrace_append hprefix tailTrace_370871
  have hstable : (prefixWord ++ tailWord_370871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370871).length < 2 ^ (prefixWord ++ tailWord_370871).sum := by decide
  have hdescent : baseEnd_370871 < baseStart_370871 := by decide
  rcases family_descends (prefixWord ++ tailWord_370871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370885 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 3]
def baseStart_370885 : Nat := 118140960795 + 370885 * 2 ^ 59
def prefixEnd_370885 : Nat := 4983230072969 + 3 ^ 40 * 370885 * 2
def baseEnd_370885 : Nat := 190442272542886644431837

theorem tailTrace_370885 : CollatzResearch.WordTrace tailWord_370885 prefixEnd_370885 190442272542886644431837 := by
  unfold tailWord_370885
  simp only [CollatzResearch.WordTrace]
  refine ⟨13527287261354461960186109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9018191507569641306790739 13527287261354461960186109)
  ·
    refine ⟨5072732723007923235069791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13527287261354461960186109 5072732723007923235069791)
    ·
      refine ⟨7609099084511884852604687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5072732723007923235069791 7609099084511884852604687)
      ·
        refine ⟨11413648626767827278907031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7609099084511884852604687 11413648626767827278907031)
        ·
          refine ⟨17120472940151740918360547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11413648626767827278907031 17120472940151740918360547)
          ·
            refine ⟨25680709410227611377540821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17120472940151740918360547 25680709410227611377540821)
            ·
              refine ⟨601891626802209641661113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25680709410227611377540821 601891626802209641661113)
              ·
                refine ⟨451418720101657231245835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 601891626802209641661113 451418720101657231245835)
                ·
                  refine ⟨677128080152485846868753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451418720101657231245835 677128080152485846868753)
                  ·
                    refine ⟨507846060114364385151565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 677128080152485846868753 507846060114364385151565)
                    ·
                      refine ⟨190442272542886644431837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 507846060114364385151565 190442272542886644431837)
                      ·
                        rfl

theorem cell23_370885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 3].length) (baseStart_370885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370885 prefixEnd_370885 := by exact prefixLift 370885
  have htrace : WordTrace (prefixWord ++ tailWord_370885) baseStart_370885 baseEnd_370885 := by
    simpa [prefixWord, tailWord_370885, baseEnd_370885] using wordTrace_append hprefix tailTrace_370885
  have hstable : (prefixWord ++ tailWord_370885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370885).length < 2 ^ (prefixWord ++ tailWord_370885).sum := by decide
  have hdescent : baseEnd_370885 < baseStart_370885 := by decide
  rcases family_descends (prefixWord ++ tailWord_370885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370902 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_370902 : Nat := 118140960795 + 370902 * 2 ^ 59
def prefixEnd_370902 : Nat := 4983230072969 + 3 ^ 40 * 370902 * 2
def baseEnd_370902 : Nat := 190451001714013077919259

theorem tailTrace_370902 : CollatzResearch.WordTrace tailWord_370902 prefixEnd_370902 190451001714013077919259 := by
  unfold tailWord_370902
  simp only [CollatzResearch.WordTrace]
  refine ⟨845494206393304616472185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9018604868195249242369973 845494206393304616472185)
  ·
    refine ⟨634120654794978462354139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 845494206393304616472185 634120654794978462354139)
    ·
      refine ⟨951180982192467693531209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634120654794978462354139 951180982192467693531209)
      ·
        refine ⟨713385736644350770148407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951180982192467693531209 713385736644350770148407)
        ·
          refine ⟨1070078604966526155222611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713385736644350770148407 1070078604966526155222611)
          ·
            refine ⟨1605117907449789232833917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070078604966526155222611 1605117907449789232833917)
            ·
              refine ⟨601919215293670962312719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1605117907449789232833917 601919215293670962312719)
              ·
                refine ⟨902878822940506443469079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 601919215293670962312719 902878822940506443469079)
                ·
                  refine ⟨1354318234410759665203619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902878822940506443469079 1354318234410759665203619)
                  ·
                    refine ⟨2031477351616139497805429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1354318234410759665203619 2031477351616139497805429)
                    ·
                      refine ⟨190451001714013077919259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2031477351616139497805429 190451001714013077919259)
                      ·
                        rfl

theorem cell23_370902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_370902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370902 prefixEnd_370902 := by exact prefixLift 370902
  have htrace : WordTrace (prefixWord ++ tailWord_370902) baseStart_370902 baseEnd_370902 := by
    simpa [prefixWord, tailWord_370902, baseEnd_370902] using wordTrace_append hprefix tailTrace_370902
  have hstable : (prefixWord ++ tailWord_370902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370902).length < 2 ^ (prefixWord ++ tailWord_370902).sum := by decide
  have hdescent : baseEnd_370902 < baseStart_370902 := by decide
  rcases family_descends (prefixWord ++ tailWord_370902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370942 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_370942 : Nat := 118140960795 + 370942 * 2 ^ 59
def prefixEnd_370942 : Nat := 4983230072969 + 3 ^ 40 * 370942 * 2
def baseEnd_370942 : Nat := 190471540940192921419075

theorem tailTrace_370942 : CollatzResearch.WordTrace tailWord_370942 prefixEnd_370942 190471540940192921419075 := by
  unfold tailWord_370942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691170777768495086876385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9019577481431973796674053 1691170777768495086876385)
  ·
    refine ⟨1268378083326371315157289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1691170777768495086876385 1268378083326371315157289)
    ·
      refine ⟨951283562494778486367967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1268378083326371315157289 951283562494778486367967)
      ·
        refine ⟨1426925343742167729551951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951283562494778486367967 1426925343742167729551951)
        ·
          refine ⟨2140388015613251594327927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426925343742167729551951 2140388015613251594327927)
          ·
            refine ⟨3210582023419877391491891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140388015613251594327927 3210582023419877391491891)
            ·
              refine ⟨4815873035129816087237837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210582023419877391491891 4815873035129816087237837)
              ·
                refine ⟨1805952388173681032714189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4815873035129816087237837 1805952388173681032714189)
                ·
                  refine ⟨677232145565130387267821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1805952388173681032714189 677232145565130387267821)
                  ·
                    refine ⟨253962054586923895225433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 677232145565130387267821 253962054586923895225433)
                    ·
                      refine ⟨190471540940192921419075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 253962054586923895225433 190471540940192921419075)
                      ·
                        rfl

theorem cell23_370942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_370942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370942 prefixEnd_370942 := by exact prefixLift 370942
  have htrace : WordTrace (prefixWord ++ tailWord_370942) baseStart_370942 baseEnd_370942 := by
    simpa [prefixWord, tailWord_370942, baseEnd_370942] using wordTrace_append hprefix tailTrace_370942
  have hstable : (prefixWord ++ tailWord_370942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370942).length < 2 ^ (prefixWord ++ tailWord_370942).sum := by decide
  have hdescent : baseEnd_370942 < baseStart_370942 := by decide
  rcases family_descends (prefixWord ++ tailWord_370942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370955 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 1, 4, 2]
def baseStart_370955 : Nat := 118140960795 + 370955 * 2 ^ 59
def prefixEnd_370955 : Nat := 4983230072969 + 3 ^ 40 * 370955 * 2
def baseEnd_370955 : Nat := 190478216188701370556515

theorem tailTrace_370955 : CollatzResearch.WordTrace tailWord_370955 prefixEnd_370955 190478216188701370556515 := by
  unfold tailWord_370955
  simp only [CollatzResearch.WordTrace]
  refine ⟨13529840371100863915234319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9019893580733909276822879 13529840371100863915234319)
  ·
    refine ⟨20294760556651295872851479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13529840371100863915234319 20294760556651295872851479)
    ·
      refine ⟨30442140834976943809277219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20294760556651295872851479 30442140834976943809277219)
      ·
        refine ⟨45663211252465415713915829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30442140834976943809277219 45663211252465415713915829)
        ·
          refine ⟨4280926054918632723179609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45663211252465415713915829 4280926054918632723179609)
          ·
            refine ⟨3210694541188974542384707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280926054918632723179609 3210694541188974542384707)
            ·
              refine ⟨4816041811783461813577061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210694541188974542384707 4816041811783461813577061)
              ·
                refine ⟨903007839709399090045699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4816041811783461813577061 903007839709399090045699)
                ·
                  refine ⟨1354511759564098635068549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903007839709399090045699 1354511759564098635068549)
                  ·
                    refine ⟨253970954918268494075353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354511759564098635068549 253970954918268494075353)
                    ·
                      refine ⟨190478216188701370556515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 253970954918268494075353 190478216188701370556515)
                      ·
                        rfl

theorem cell23_370955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 4, 2].length) (baseStart_370955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370955 prefixEnd_370955 := by exact prefixLift 370955
  have htrace : WordTrace (prefixWord ++ tailWord_370955) baseStart_370955 baseEnd_370955 := by
    simpa [prefixWord, tailWord_370955, baseEnd_370955] using wordTrace_append hprefix tailTrace_370955
  have hstable : (prefixWord ++ tailWord_370955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370955).length < 2 ^ (prefixWord ++ tailWord_370955).sum := by decide
  have hdescent : baseEnd_370955 < baseStart_370955 := by decide
  rcases family_descends (prefixWord ++ tailWord_370955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370958 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_370958 : Nat := 118140960795 + 370958 * 2 ^ 59
def prefixEnd_370958 : Nat := 4983230072969 + 3 ^ 40 * 370958 * 2
def baseEnd_370958 : Nat := 190479756630664858819001

theorem tailTrace_370958 : CollatzResearch.WordTrace tailWord_370958 prefixEnd_370958 190479756630664858819001 := by
  unfold tailWord_370958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1691243723761249428449191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9019966526726663618395685 1691243723761249428449191)
  ·
    refine ⟨2536865585641874142673787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1691243723761249428449191 2536865585641874142673787)
    ·
      refine ⟨3805298378462811214010681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2536865585641874142673787 3805298378462811214010681)
      ·
        refine ⟨2853973783847108410508011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3805298378462811214010681 2853973783847108410508011)
        ·
          refine ⟨4280960675770662615762017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853973783847108410508011 4280960675770662615762017)
          ·
            refine ⟨3210720506827996961821513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280960675770662615762017 3210720506827996961821513)
            ·
              refine ⟨2408040380120997721366135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3210720506827996961821513 2408040380120997721366135)
              ·
                refine ⟨3612060570181496582049203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408040380120997721366135 3612060570181496582049203)
                ·
                  refine ⟨5418090855272244873073805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3612060570181496582049203 5418090855272244873073805)
                  ·
                    refine ⟨2031784070727091827402677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5418090855272244873073805 2031784070727091827402677)
                    ·
                      refine ⟨190479756630664858819001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2031784070727091827402677 190479756630664858819001)
                      ·
                        rfl

theorem cell23_370958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_370958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370958 prefixEnd_370958 := by exact prefixLift 370958
  have htrace : WordTrace (prefixWord ++ tailWord_370958) baseStart_370958 baseEnd_370958 := by
    simpa [prefixWord, tailWord_370958, baseEnd_370958] using wordTrace_append hprefix tailTrace_370958
  have hstable : (prefixWord ++ tailWord_370958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370958).length < 2 ^ (prefixWord ++ tailWord_370958).sum := by decide
  have hdescent : baseEnd_370958 < baseStart_370958 := by decide
  rcases family_descends (prefixWord ++ tailWord_370958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370968 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_370968 : Nat := 118140960795 + 370968 * 2 ^ 59
def prefixEnd_370968 : Nat := 4983230072969 + 3 ^ 40 * 370968 * 2
def baseEnd_370968 : Nat := 190484891437209819693955

theorem tailTrace_370968 : CollatzResearch.WordTrace tailWord_370968 prefixEnd_370968 190484891437209819693955 := by
  unfold tailWord_370968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765157260026883567728779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9020209680035844756971705 6765157260026883567728779)
  ·
    refine ⟨10147735890040325351593169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6765157260026883567728779 10147735890040325351593169)
    ·
      refine ⟨7610801917530244013694877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10147735890040325351593169 7610801917530244013694877)
      ·
        refine ⟨2854050719073841505135579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7610801917530244013694877 2854050719073841505135579)
        ·
          refine ⟨4281076078610762257703369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854050719073841505135579 4281076078610762257703369)
          ·
            refine ⟨3210807058958071693277527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4281076078610762257703369 3210807058958071693277527)
            ·
              refine ⟨4816210588437107539916291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210807058958071693277527 4816210588437107539916291)
              ·
                refine ⟨7224315882655661309874437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4816210588437107539916291 7224315882655661309874437)
                ·
                  refine ⟨1354559227997936495601457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7224315882655661309874437 1354559227997936495601457)
                  ·
                    refine ⟨1015919420998452371701093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1354559227997936495601457 1015919420998452371701093)
                    ·
                      refine ⟨190484891437209819693955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1015919420998452371701093 190484891437209819693955)
                      ·
                        rfl

theorem cell23_370968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_370968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370968 prefixEnd_370968 := by exact prefixLift 370968
  have htrace : WordTrace (prefixWord ++ tailWord_370968) baseStart_370968 baseEnd_370968 := by
    simpa [prefixWord, tailWord_370968, baseEnd_370968] using wordTrace_append hprefix tailTrace_370968
  have hstable : (prefixWord ++ tailWord_370968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370968).length < 2 ^ (prefixWord ++ tailWord_370968).sum := by decide
  have hdescent : baseEnd_370968 < baseStart_370968 := by decide
  rcases family_descends (prefixWord ++ tailWord_370968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_370983 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_370983 : Nat := 118140960795 + 370983 * 2 ^ 59
def prefixEnd_370983 : Nat := 4983230072969 + 3 ^ 40 * 370983 * 2
def baseEnd_370983 : Nat := 190492593647027261006387

theorem tailTrace_370983 : CollatzResearch.WordTrace tailWord_370983 prefixEnd_370983 190492593647027261006387 := by
  unfold tailWord_370983
  simp only [CollatzResearch.WordTrace]
  refine ⟨13530861614999424697253603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9020574409999616464835735 13530861614999424697253603)
  ·
    refine ⟨20296292422499137045880405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13530861614999424697253603 20296292422499137045880405)
    ·
      refine ⟨237847176826161762256411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 20296292422499137045880405 237847176826161762256411)
      ·
        refine ⟨356770765239242643384617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237847176826161762256411 356770765239242643384617)
        ·
          refine ⟨267578073929431982538463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 356770765239242643384617 267578073929431982538463)
          ·
            refine ⟨401367110894147973807695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267578073929431982538463 401367110894147973807695)
            ·
              refine ⟨602050666341221960711543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401367110894147973807695 602050666341221960711543)
              ·
                refine ⟨903075999511832941067315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602050666341221960711543 903075999511832941067315)
                ·
                  refine ⟨1354613999267749411600973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903075999511832941067315 1354613999267749411600973)
                  ·
                    refine ⟨507980249725406029350365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354613999267749411600973 507980249725406029350365)
                    ·
                      refine ⟨190492593647027261006387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 507980249725406029350365 190492593647027261006387)
                      ·
                        rfl

theorem cell23_370983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_370983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_370983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_370983 prefixEnd_370983 := by exact prefixLift 370983
  have htrace : WordTrace (prefixWord ++ tailWord_370983) baseStart_370983 baseEnd_370983 := by
    simpa [prefixWord, tailWord_370983, baseEnd_370983] using wordTrace_append hprefix tailTrace_370983
  have hstable : (prefixWord ++ tailWord_370983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_370983).length < 2 ^ (prefixWord ++ tailWord_370983).sum := by decide
  have hdescent : baseEnd_370983 < baseStart_370983 := by decide
  rcases family_descends (prefixWord ++ tailWord_370983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371025 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 2, 5]
def baseStart_371025 : Nat := 118140960795 + 371025 * 2 ^ 59
def prefixEnd_371025 : Nat := 4983230072969 + 3 ^ 40 * 371025 * 2
def baseEnd_371025 : Nat := 63504719944838698893731

theorem tailTrace_371025 : CollatzResearch.WordTrace tailWord_371025 prefixEnd_371025 63504719944838698893731 := by
  unfold tailWord_371025
  simp only [CollatzResearch.WordTrace]
  refine ⟨13532393480847265870282529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9021595653898177246855019 13532393480847265870282529)
  ·
    refine ⟨10149295110635449402711897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13532393480847265870282529 10149295110635449402711897)
    ·
      refine ⟨7611971332976587052033923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10149295110635449402711897 7611971332976587052033923)
      ·
        refine ⟨11417956999464880578050885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7611971332976587052033923 11417956999464880578050885)
        ·
          refine ⟨2140866937399665108384541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11417956999464880578050885 2140866937399665108384541)
          ·
            refine ⟨802825101524874415644203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2140866937399665108384541 802825101524874415644203)
            ·
              refine ⟨1204237652287311623466305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 802825101524874415644203 1204237652287311623466305)
              ·
                refine ⟨903178239215483717599729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204237652287311623466305 903178239215483717599729)
                ·
                  refine ⟨677383679411612788199797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 903178239215483717599729 677383679411612788199797)
                  ·
                    refine ⟨63504719944838698893731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 677383679411612788199797 63504719944838698893731)
                    ·
                      rfl

theorem cell23_371025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_371025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371025 prefixEnd_371025 := by exact prefixLift 371025
  have htrace : WordTrace (prefixWord ++ tailWord_371025) baseStart_371025 baseEnd_371025 := by
    simpa [prefixWord, tailWord_371025, baseEnd_371025] using wordTrace_append hprefix tailTrace_371025
  have hstable : (prefixWord ++ tailWord_371025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371025).length < 2 ^ (prefixWord ++ tailWord_371025).sum := by decide
  have hdescent : baseEnd_371025 < baseStart_371025 := by decide
  rcases family_descends (prefixWord ++ tailWord_371025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371029 : List Nat := [1, 3, 2, 2, 4, 1, 3, 2, 5]
def baseStart_371029 : Nat := 118140960795 + 371029 * 2 ^ 59
def prefixEnd_371029 : Nat := 4983230072969 + 3 ^ 40 * 371029 * 2
def baseEnd_371029 : Nat := 21168468195237120114575

theorem tailTrace_371029 : CollatzResearch.WordTrace tailWord_371029 prefixEnd_371029 21168468195237120114575 := by
  unfold tailWord_371029
  simp only [CollatzResearch.WordTrace]
  refine ⟨13532539372832774553428141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9021692915221849702285427 13532539372832774553428141)
  ·
    refine ⟨5074702264812290457535553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13532539372832774553428141 5074702264812290457535553)
    ·
      refine ⟨3806026698609217843151665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5074702264812290457535553 3806026698609217843151665)
      ·
        refine ⟨2854520023956913382363749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3806026698609217843151665 2854520023956913382363749)
        ·
          refine ⟨535222504491921259193203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2854520023956913382363749 535222504491921259193203)
          ·
            refine ⟨802833756737881888789805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535222504491921259193203 802833756737881888789805)
            ·
              refine ⟨301062658776705708296177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802833756737881888789805 301062658776705708296177)
              ·
                refine ⟨225796994082529281222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301062658776705708296177 225796994082529281222133)
                ·
                  refine ⟨21168468195237120114575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225796994082529281222133 21168468195237120114575)
                  ·
                    rfl

theorem cell23_371029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_371029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371029 prefixEnd_371029 := by exact prefixLift 371029
  have htrace : WordTrace (prefixWord ++ tailWord_371029) baseStart_371029 baseEnd_371029 := by
    simpa [prefixWord, tailWord_371029, baseEnd_371029] using wordTrace_append hprefix tailTrace_371029
  have hstable : (prefixWord ++ tailWord_371029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371029).length < 2 ^ (prefixWord ++ tailWord_371029).sum := by decide
  have hdescent : baseEnd_371029 < baseStart_371029 := by decide
  rcases family_descends (prefixWord ++ tailWord_371029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371068 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 8]
def baseStart_371068 : Nat := 118140960795 + 371068 * 2 ^ 59
def prefixEnd_371068 : Nat := 4983230072969 + 3 ^ 40 * 371068 * 2
def baseEnd_371068 : Nat := 21170693278073269827055

theorem tailTrace_371068 : CollatzResearch.WordTrace tailWord_371068 prefixEnd_371068 21170693278073269827055 := by
  unfold tailWord_371068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766980909845742107048929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9022641213127656142731905 6766980909845742107048929)
  ·
    refine ⟨5075235682384306580286697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6766980909845742107048929 5075235682384306580286697)
    ·
      refine ⟨3806426761788229935215023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5075235682384306580286697 3806426761788229935215023)
      ·
        refine ⟨5709640142682344902822535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806426761788229935215023 5709640142682344902822535)
        ·
          refine ⟨8564460214023517354233803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5709640142682344902822535 8564460214023517354233803)
          ·
            refine ⟨12846690321035276031350705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8564460214023517354233803 12846690321035276031350705)
            ·
              refine ⟨9635017740776457023513029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12846690321035276031350705 9635017740776457023513029)
              ·
                refine ⟨1806565826395585691908693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9635017740776457023513029 1806565826395585691908693)
                ·
                  refine ⟨21170693278073269827055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1806565826395585691908693 21170693278073269827055)
                  ·
                    rfl

theorem cell23_371068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_371068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371068 prefixEnd_371068 := by exact prefixLift 371068
  have htrace : WordTrace (prefixWord ++ tailWord_371068) baseStart_371068 baseEnd_371068 := by
    simpa [prefixWord, tailWord_371068, baseEnd_371068] using wordTrace_append hprefix tailTrace_371068
  have hstable : (prefixWord ++ tailWord_371068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371068).length < 2 ^ (prefixWord ++ tailWord_371068).sum := by decide
  have hdescent : baseEnd_371068 < baseStart_371068 := by decide
  rcases family_descends (prefixWord ++ tailWord_371068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371122 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2]
def baseStart_371122 : Nat := 118140960795 + 371122 * 2 ^ 59
def prefixEnd_371122 : Nat := 4983230072969 + 3 ^ 40 * 371122 * 2
def baseEnd_371122 : Nat := 190563967458002217168247

theorem tailTrace_371122 : CollatzResearch.WordTrace tailWord_371122 prefixEnd_371122 190563967458002217168247 := by
  unfold tailWord_371122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3383982840373962859140905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9023954240997234291042413 3383982840373962859140905)
  ·
    refine ⟨2537987130280472144355679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3383982840373962859140905 2537987130280472144355679)
    ·
      refine ⟨3806980695420708216533519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2537987130280472144355679 3806980695420708216533519)
      ·
        refine ⟨5710471043131062324800279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806980695420708216533519 5710471043131062324800279)
        ·
          refine ⟨8565706564696593487200419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710471043131062324800279 8565706564696593487200419)
          ·
            refine ⟨12848559847044890230800629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8565706564696593487200419 12848559847044890230800629)
            ·
              refine ⟨1204552485660458459137559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12848559847044890230800629 1204552485660458459137559)
              ·
                refine ⟨1806828728490687688706339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204552485660458459137559 1806828728490687688706339)
                ·
                  refine ⟨2710243092736031533059509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806828728490687688706339 2710243092736031533059509)
                  ·
                    refine ⟨254085289944002956224329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2710243092736031533059509 254085289944002956224329)
                    ·
                      refine ⟨190563967458002217168247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254085289944002956224329 190563967458002217168247)
                      ·
                        rfl

theorem cell23_371122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_371122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371122 prefixEnd_371122 := by exact prefixLift 371122
  have htrace : WordTrace (prefixWord ++ tailWord_371122) baseStart_371122 baseEnd_371122 := by
    simpa [prefixWord, tailWord_371122, baseEnd_371122] using wordTrace_append hprefix tailTrace_371122
  have hstable : (prefixWord ++ tailWord_371122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371122).length < 2 ^ (prefixWord ++ tailWord_371122).sum := by decide
  have hdescent : baseEnd_371122 < baseStart_371122 := by decide
  rcases family_descends (prefixWord ++ tailWord_371122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371169 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_371169 : Nat := 118140960795 + 371169 * 2 ^ 59
def prefixEnd_371169 : Nat := 4983230072969 + 3 ^ 40 * 371169 * 2
def baseEnd_371169 : Nat := 190588101048763533280531

theorem tailTrace_371169 : CollatzResearch.WordTrace tailWord_371169 prefixEnd_371169 190588101048763533280531 := by
  unfold tailWord_371169
  simp only [CollatzResearch.WordTrace]
  refine ⟨13537645592325578463524561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9025097061550385642349707 13537645592325578463524561)
  ·
    refine ⟨10153234194244183847643421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13537645592325578463524561 10153234194244183847643421)
    ·
      refine ⟨3807462822841568942866283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10153234194244183847643421 3807462822841568942866283)
      ·
        refine ⟨5711194234262353414299425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807462822841568942866283 5711194234262353414299425)
        ·
          refine ⟨4283395675696765060724569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5711194234262353414299425 4283395675696765060724569)
          ·
            refine ⟨3212546756772573795543427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4283395675696765060724569 3212546756772573795543427)
            ·
              refine ⟨4818820135158860693315141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212546756772573795543427 4818820135158860693315141)
              ·
                refine ⟨903528775342286379996589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4818820135158860693315141 903528775342286379996589)
                ·
                  refine ⟨338823290753357392498721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 903528775342286379996589 338823290753357392498721)
                  ·
                    refine ⟨254117468065018044374041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 338823290753357392498721 254117468065018044374041)
                    ·
                      refine ⟨190588101048763533280531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254117468065018044374041 190588101048763533280531)
                      ·
                        rfl

theorem cell23_371169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_371169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371169 prefixEnd_371169 := by exact prefixLift 371169
  have htrace : WordTrace (prefixWord ++ tailWord_371169) baseStart_371169 baseEnd_371169 := by
    simpa [prefixWord, tailWord_371169, baseEnd_371169] using wordTrace_append hprefix tailTrace_371169
  have hstable : (prefixWord ++ tailWord_371169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371169).length < 2 ^ (prefixWord ++ tailWord_371169).sum := by decide
  have hdescent : baseEnd_371169 < baseStart_371169 := by decide
  rcases family_descends (prefixWord ++ tailWord_371169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371175 : List Nat := [1, 1, 5, 2, 1, 1, 3, 9]
def baseStart_371175 : Nat := 118140960795 + 371175 * 2 ^ 59
def prefixEnd_371175 : Nat := 4983230072969 + 3 ^ 40 * 371175 * 2
def baseEnd_371175 : Nat := 7058932664173722585389

theorem tailTrace_371175 : CollatzResearch.WordTrace tailWord_371175 prefixEnd_371175 7058932664173722585389 := by
  unfold tailWord_371175
  simp only [CollatzResearch.WordTrace]
  refine ⟨13537864430303841488242979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9025242953535894325495319 13537864430303841488242979)
  ·
    refine ⟨20306796645455762232364469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13537864430303841488242979 20306796645455762232364469)
    ·
      refine ⟨1903762185511477709284169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20306796645455762232364469 1903762185511477709284169)
      ·
        refine ⟨1427821639133608281963127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1903762185511477709284169 1427821639133608281963127)
        ·
          refine ⟨2141732458700412422944691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427821639133608281963127 2141732458700412422944691)
          ·
            refine ⟨3212598688050618634417037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141732458700412422944691 3212598688050618634417037)
            ·
              refine ⟨1204724508018981987906389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3212598688050618634417037 1204724508018981987906389)
              ·
                refine ⟨7058932664173722585389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1204724508018981987906389 7058932664173722585389)
                ·
                  rfl

theorem cell23_371175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 9].length) (baseStart_371175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371175 prefixEnd_371175 := by exact prefixLift 371175
  have htrace : WordTrace (prefixWord ++ tailWord_371175) baseStart_371175 baseEnd_371175 := by
    simpa [prefixWord, tailWord_371175, baseEnd_371175] using wordTrace_append hprefix tailTrace_371175
  have hstable : (prefixWord ++ tailWord_371175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371175).length < 2 ^ (prefixWord ++ tailWord_371175).sum := by decide
  have hdescent : baseEnd_371175 < baseStart_371175 := by decide
  rcases family_descends (prefixWord ++ tailWord_371175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371203 : List Nat := [1, 1, 1, 3, 2, 1, 7, 2, 1, 2, 2]
def baseStart_371203 : Nat := 118140960795 + 371203 * 2 ^ 59
def prefixEnd_371203 : Nat := 4983230072969 + 3 ^ 40 * 371203 * 2
def baseEnd_371203 : Nat := 190605559391016400255375

theorem tailTrace_371203 : CollatzResearch.WordTrace tailWord_371203 prefixEnd_371203 190605559391016400255375 := by
  unfold tailWord_371203
  simp only [CollatzResearch.WordTrace]
  refine ⟨13538885674202402270262263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9025923782801601513508175 13538885674202402270262263)
  ·
    refine ⟨20308328511303603405393395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13538885674202402270262263 20308328511303603405393395)
    ·
      refine ⟨30462492766955405108090093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20308328511303603405393395 30462492766955405108090093)
      ·
        refine ⟨11423434787608276915533785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30462492766955405108090093 11423434787608276915533785)
        ·
          refine ⟨8567576090706207686650339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11423434787608276915533785 8567576090706207686650339)
          ·
            refine ⟨12851364136059311529975509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8567576090706207686650339 12851364136059311529975509)
            ·
              refine ⟨301203846938890113983801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12851364136059311529975509 301203846938890113983801)
              ·
                refine ⟨225902885204167585487851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301203846938890113983801 225902885204167585487851)
                ·
                  refine ⟨338854327806251378231777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225902885204167585487851 338854327806251378231777)
                  ·
                    refine ⟨254140745854688533673833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 338854327806251378231777 254140745854688533673833)
                    ·
                      refine ⟨190605559391016400255375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254140745854688533673833 190605559391016400255375)
                      ·
                        rfl

theorem cell23_371203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_371203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371203 prefixEnd_371203 := by exact prefixLift 371203
  have htrace : WordTrace (prefixWord ++ tailWord_371203) baseStart_371203 baseEnd_371203 := by
    simpa [prefixWord, tailWord_371203, baseEnd_371203] using wordTrace_append hprefix tailTrace_371203
  have hstable : (prefixWord ++ tailWord_371203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371203).length < 2 ^ (prefixWord ++ tailWord_371203).sum := by decide
  have hdescent : baseEnd_371203 < baseStart_371203 := by decide
  rcases family_descends (prefixWord ++ tailWord_371203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371213 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_371213 : Nat := 118140960795 + 371213 * 2 ^ 59
def prefixEnd_371213 : Nat := 4983230072969 + 3 ^ 40 * 371213 * 2
def baseEnd_371213 : Nat := 63536898065853787043443

theorem tailTrace_371213 : CollatzResearch.WordTrace tailWord_371213 prefixEnd_371213 63536898065853787043443 := by
  unfold tailWord_371213
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539250404166173978126293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9026166936110782652084195 13539250404166173978126293)
  ·
    refine ⟨317326181347644702612335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13539250404166173978126293 317326181347644702612335)
    ·
      refine ⟨475989272021467053918503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317326181347644702612335 475989272021467053918503)
      ·
        refine ⟨713983908032200580877755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475989272021467053918503 713983908032200580877755)
        ·
          refine ⟨1070975862048300871316633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713983908032200580877755 1070975862048300871316633)
          ·
            refine ⟨803231896536225653487475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070975862048300871316633 803231896536225653487475)
            ·
              refine ⟨1204847844804338480231213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803231896536225653487475 1204847844804338480231213)
              ·
                refine ⟨451817941801626930086705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204847844804338480231213 451817941801626930086705)
                ·
                  refine ⟨338863456351220197565029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451817941801626930086705 338863456351220197565029)
                  ·
                    refine ⟨63536898065853787043443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 338863456351220197565029 63536898065853787043443)
                    ·
                      rfl

theorem cell23_371213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_371213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371213 prefixEnd_371213 := by exact prefixLift 371213
  have htrace : WordTrace (prefixWord ++ tailWord_371213) baseStart_371213 baseEnd_371213 := by
    simpa [prefixWord, tailWord_371213, baseEnd_371213] using wordTrace_append hprefix tailTrace_371213
  have hstable : (prefixWord ++ tailWord_371213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371213).length < 2 ^ (prefixWord ++ tailWord_371213).sum := by decide
  have hdescent : baseEnd_371213 < baseStart_371213 := by decide
  rcases family_descends (prefixWord ++ tailWord_371213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371219 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 3]
def baseStart_371219 : Nat := 118140960795 + 371219 * 2 ^ 59
def prefixEnd_371219 : Nat := 4983230072969 + 3 ^ 40 * 371219 * 2
def baseEnd_371219 : Nat := 190613775081488337655301

theorem tailTrace_371219 : CollatzResearch.WordTrace tailWord_371219 prefixEnd_371219 190613775081488337655301 := by
  unfold tailWord_371219
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539469242144437002844711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9026312828096291335229807 13539469242144437002844711)
  ·
    refine ⟨20309203863216655504267067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13539469242144437002844711 20309203863216655504267067)
    ·
      refine ⟨30463805794824983256400601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20309203863216655504267067 30463805794824983256400601)
      ·
        refine ⟨22847854346118737442300451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30463805794824983256400601 22847854346118737442300451)
        ·
          refine ⟨34271781519178106163450677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22847854346118737442300451 34271781519178106163450677)
          ·
            refine ⟨3212979517422947452823501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34271781519178106163450677 3212979517422947452823501)
            ·
              refine ⟨1204867319033605294808813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3212979517422947452823501 1204867319033605294808813)
              ·
                refine ⟨451825244637601985553305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1204867319033605294808813 451825244637601985553305)
                ·
                  refine ⟨338868933478201489164979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451825244637601985553305 338868933478201489164979)
                  ·
                    refine ⟨508303400217302233747469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 338868933478201489164979 508303400217302233747469)
                    ·
                      refine ⟨190613775081488337655301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 508303400217302233747469 190613775081488337655301)
                      ·
                        rfl

theorem cell23_371219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 1, 3].length) (baseStart_371219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371219 prefixEnd_371219 := by exact prefixLift 371219
  have htrace : WordTrace (prefixWord ++ tailWord_371219) baseStart_371219 baseEnd_371219 := by
    simpa [prefixWord, tailWord_371219, baseEnd_371219] using wordTrace_append hprefix tailTrace_371219
  have hstable : (prefixWord ++ tailWord_371219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371219).length < 2 ^ (prefixWord ++ tailWord_371219).sum := by decide
  have hdescent : baseEnd_371219 < baseStart_371219 := by decide
  rcases family_descends (prefixWord ++ tailWord_371219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371223 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_371223 : Nat := 118140960795 + 371223 * 2 ^ 59
def prefixEnd_371223 : Nat := 4983230072969 + 3 ^ 40 * 371223 * 2
def baseEnd_371223 : Nat := 190615829004106322005283

theorem tailTrace_371223 : CollatzResearch.WordTrace tailWord_371223 prefixEnd_371223 190615829004106322005283 := by
  unfold tailWord_371223
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539615134129945685990323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9026410089419963790660215 13539615134129945685990323)
  ·
    refine ⟨20309422701194918528985485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13539615134129945685990323 20309422701194918528985485)
    ·
      refine ⟨7616033512948094448369557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20309422701194918528985485 7616033512948094448369557)
      ·
        refine ⟨357001570919441927267323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7616033512948094448369557 357001570919441927267323)
        ·
          refine ⟨535502356379162890900985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357001570919441927267323 535502356379162890900985)
          ·
            refine ⟨401626767284372168175739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535502356379162890900985 401626767284372168175739)
            ·
              refine ⟨602440150926558252263609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401626767284372168175739 602440150926558252263609)
              ·
                refine ⟨451830113194918689197707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602440150926558252263609 451830113194918689197707)
                ·
                  refine ⟨677745169792378033796561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 451830113194918689197707 677745169792378033796561)
                  ·
                    refine ⟨508308877344283525347421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 677745169792378033796561 508308877344283525347421)
                    ·
                      refine ⟨190615829004106322005283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 508308877344283525347421 190615829004106322005283)
                      ·
                        rfl

theorem cell23_371223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_371223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371223 prefixEnd_371223 := by exact prefixLift 371223
  have htrace : WordTrace (prefixWord ++ tailWord_371223) baseStart_371223 baseEnd_371223 := by
    simpa [prefixWord, tailWord_371223, baseEnd_371223] using wordTrace_append hprefix tailTrace_371223
  have hstable : (prefixWord ++ tailWord_371223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371223).length < 2 ^ (prefixWord ++ tailWord_371223).sum := by decide
  have hdescent : baseEnd_371223 < baseStart_371223 := by decide
  rcases family_descends (prefixWord ++ tailWord_371223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371225 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_371225 : Nat := 118140960795 + 371225 * 2 ^ 59
def prefixEnd_371225 : Nat := 4983230072969 + 3 ^ 40 * 371225 * 2
def baseEnd_371225 : Nat := 190616855965415314180273

theorem tailTrace_371225 : CollatzResearch.WordTrace tailWord_371225 prefixEnd_371225 190616855965415314180273 := by
  unfold tailWord_371225
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539688080122700027563129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9026458720081800018375419 13539688080122700027563129)
  ·
    refine ⟨10154766060092025020672347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13539688080122700027563129 10154766060092025020672347)
    ·
      refine ⟨15232149090138037531008521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10154766060092025020672347 15232149090138037531008521)
      ·
        refine ⟨11424111817603528148256391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15232149090138037531008521 11424111817603528148256391)
        ·
          refine ⟨17136167726405292222384587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11424111817603528148256391 17136167726405292222384587)
          ·
            refine ⟨25704251589607938333576881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17136167726405292222384587 25704251589607938333576881)
            ·
              refine ⟨19278188692205953750182661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25704251589607938333576881 19278188692205953750182661)
              ·
                refine ⟨3614660379788616328159249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19278188692205953750182661 3614660379788616328159249)
                ·
                  refine ⟨2710995284841462246119437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3614660379788616328159249 2710995284841462246119437)
                  ·
                    refine ⟨1016623231815548342294789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2710995284841462246119437 1016623231815548342294789)
                    ·
                      refine ⟨190616855965415314180273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1016623231815548342294789 190616855965415314180273)
                      ·
                        rfl

theorem cell23_371225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_371225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371225 prefixEnd_371225 := by exact prefixLift 371225
  have htrace : WordTrace (prefixWord ++ tailWord_371225) baseStart_371225 baseEnd_371225 := by
    simpa [prefixWord, tailWord_371225, baseEnd_371225] using wordTrace_append hprefix tailTrace_371225
  have hstable : (prefixWord ++ tailWord_371225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371225).length < 2 ^ (prefixWord ++ tailWord_371225).sum := by decide
  have hdescent : baseEnd_371225 < baseStart_371225 := by decide
  rcases family_descends (prefixWord ++ tailWord_371225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371236 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_371236 : Nat := 118140960795 + 371236 * 2 ^ 59
def prefixEnd_371236 : Nat := 4983230072969 + 3 ^ 40 * 371236 * 2
def baseEnd_371236 : Nat := 190622504252614771142723

theorem tailTrace_371236 : CollatzResearch.WordTrace tailWord_371236 prefixEnd_371236 190622504252614771142723 := by
  unfold tailWord_371236
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770044641541424453106781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9026726188721899270809041 6770044641541424453106781)
  ·
    refine ⟨2538766740578034169915043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6770044641541424453106781 2538766740578034169915043)
    ·
      refine ⟨3808150110867051254872565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538766740578034169915043 3808150110867051254872565)
      ·
        refine ⟨357014072893786055144303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3808150110867051254872565 357014072893786055144303)
        ·
          refine ⟨535521109340679082716455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357014072893786055144303 535521109340679082716455)
          ·
            refine ⟨803281664011018624074683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535521109340679082716455 803281664011018624074683)
            ·
              refine ⟨1204922496016527936112025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803281664011018624074683 1204922496016527936112025)
              ·
                refine ⟨903691872012395952084019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204922496016527936112025 903691872012395952084019)
                ·
                  refine ⟨1355537808018593928126029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903691872012395952084019 1355537808018593928126029)
                  ·
                    refine ⟨508326678006972723047261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355537808018593928126029 508326678006972723047261)
                    ·
                      refine ⟨190622504252614771142723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 508326678006972723047261 190622504252614771142723)
                      ·
                        rfl

theorem cell23_371236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_371236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371236 prefixEnd_371236 := by exact prefixLift 371236
  have htrace : WordTrace (prefixWord ++ tailWord_371236) baseStart_371236 baseEnd_371236 := by
    simpa [prefixWord, tailWord_371236, baseEnd_371236] using wordTrace_append hprefix tailTrace_371236
  have hstable : (prefixWord ++ tailWord_371236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371236).length < 2 ^ (prefixWord ++ tailWord_371236).sum := by decide
  have hdescent : baseEnd_371236 < baseStart_371236 := by decide
  rcases family_descends (prefixWord ++ tailWord_371236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371276 : List Nat := [2, 2, 1, 3, 1, 2, 1, 5, 2, 2, 2]
def baseStart_371276 : Nat := 118140960795 + 371276 * 2 ^ 59
def prefixEnd_371276 : Nat := 4983230072969 + 3 ^ 40 * 371276 * 2
def baseEnd_371276 : Nat := 190643043478794614642539

theorem tailTrace_371276 : CollatzResearch.WordTrace tailWord_371276 prefixEnd_371276 190643043478794614642539 := by
  unfold tailWord_371276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770774101468967868834841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9027698801958623825113121 6770774101468967868834841)
  ·
    refine ⟨5078080576101725901626131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6770774101468967868834841 5078080576101725901626131)
    ·
      refine ⟨7617120864152588852439197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5078080576101725901626131 7617120864152588852439197)
      ·
        refine ⟨2856420324057220819664699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7617120864152588852439197 2856420324057220819664699)
        ·
          refine ⟨4284630486085831229497049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856420324057220819664699 4284630486085831229497049)
          ·
            refine ⟨3213472864564373422122787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284630486085831229497049 3213472864564373422122787)
            ·
              refine ⟨4820209296846560133184181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213472864564373422122787 4820209296846560133184181)
              ·
                refine ⟨451894621579365012486017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4820209296846560133184181 451894621579365012486017)
                ·
                  refine ⟨338920966184523759364513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451894621579365012486017 338920966184523759364513)
                  ·
                    refine ⟨254190724638392819523385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 338920966184523759364513 254190724638392819523385)
                    ·
                      refine ⟨190643043478794614642539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254190724638392819523385 190643043478794614642539)
                      ·
                        rfl

theorem cell23_371276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_371276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371276 prefixEnd_371276 := by exact prefixLift 371276
  have htrace : WordTrace (prefixWord ++ tailWord_371276) baseStart_371276 baseEnd_371276 := by
    simpa [prefixWord, tailWord_371276, baseEnd_371276] using wordTrace_append hprefix tailTrace_371276
  have hstable : (prefixWord ++ tailWord_371276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371276).length < 2 ^ (prefixWord ++ tailWord_371276).sum := by decide
  have hdescent : baseEnd_371276 < baseStart_371276 := by decide
  rcases family_descends (prefixWord ++ tailWord_371276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371282 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 7]
def baseStart_371282 : Nat := 118140960795 + 371282 * 2 ^ 59
def prefixEnd_371282 : Nat := 4983230072969 + 3 ^ 40 * 371282 * 2
def baseEnd_371282 : Nat := 21182902706969065685279

theorem tailTrace_371282 : CollatzResearch.WordTrace tailWord_371282 prefixEnd_371282 21182902706969065685279 := by
  unfold tailWord_371282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385441760229049690597025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9027844693944132508258733 3385441760229049690597025)
  ·
    refine ⟨2539081320171787267947769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3385441760229049690597025 2539081320171787267947769)
    ·
      refine ⟨1904310990128840450960827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2539081320171787267947769 1904310990128840450960827)
      ·
        refine ⟨2856466485193260676441241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904310990128840450960827 2856466485193260676441241)
        ·
          refine ⟨2142349863894945507330931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2856466485193260676441241 2142349863894945507330931)
          ·
            refine ⟨3213524795842418260996397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142349863894945507330931 3213524795842418260996397)
            ·
              refine ⟨1205071798440906847873649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3213524795842418260996397 1205071798440906847873649)
              ·
                refine ⟨903803848830680135905237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205071798440906847873649 903803848830680135905237)
                ·
                  refine ⟨21182902706969065685279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 903803848830680135905237 21182902706969065685279)
                  ·
                    rfl

theorem cell23_371282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_371282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371282 prefixEnd_371282 := by exact prefixLift 371282
  have htrace : WordTrace (prefixWord ++ tailWord_371282) baseStart_371282 baseEnd_371282 := by
    simpa [prefixWord, tailWord_371282, baseEnd_371282] using wordTrace_append hprefix tailTrace_371282
  have hstable : (prefixWord ++ tailWord_371282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371282).length < 2 ^ (prefixWord ++ tailWord_371282).sum := by decide
  have hdescent : baseEnd_371282 < baseStart_371282 := by decide
  rcases family_descends (prefixWord ++ tailWord_371282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371299 : List Nat := [1, 1, 1, 5, 1, 2, 4, 3, 5]
def baseStart_371299 : Nat := 118140960795 + 371299 * 2 ^ 59
def prefixEnd_371299 : Nat := 4983230072969 + 3 ^ 40 * 371299 * 2
def baseEnd_371299 : Nat := 21183872614872002739437

theorem tailTrace_371299 : CollatzResearch.WordTrace tailWord_371299 prefixEnd_371299 21183872614872002739437 := by
  unfold tailWord_371299
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542387081854610665756951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9028258054569740443837967 13542387081854610665756951)
  ·
    refine ⟨20313580622781915998635427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13542387081854610665756951 20313580622781915998635427)
    ·
      refine ⟨30470370934172873997953141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20313580622781915998635427 30470370934172873997953141)
      ·
        refine ⟨2856597275078706937308107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30470370934172873997953141 2856597275078706937308107)
        ·
          refine ⟨4284895912618060405962161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856597275078706937308107 4284895912618060405962161)
          ·
            refine ⟨3213671934463545304471621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284895912618060405962161 3213671934463545304471621)
            ·
              refine ⟨602563487711914744588429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3213671934463545304471621 602563487711914744588429)
              ·
                refine ⟨225961307891968029220661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 602563487711914744588429 225961307891968029220661)
                ·
                  refine ⟨21183872614872002739437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225961307891968029220661 21183872614872002739437)
                  ·
                    rfl

theorem cell23_371299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 5].length) (baseStart_371299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371299 prefixEnd_371299 := by exact prefixLift 371299
  have htrace : WordTrace (prefixWord ++ tailWord_371299) baseStart_371299 baseEnd_371299 := by
    simpa [prefixWord, tailWord_371299, baseEnd_371299] using wordTrace_append hprefix tailTrace_371299
  have hstable : (prefixWord ++ tailWord_371299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371299).length < 2 ^ (prefixWord ++ tailWord_371299).sum := by decide
  have hdescent : baseEnd_371299 < baseStart_371299 := by decide
  rcases family_descends (prefixWord ++ tailWord_371299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371309 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_371309 : Nat := 118140960795 + 371309 * 2 ^ 59
def prefixEnd_371309 : Nat := 4983230072969 + 3 ^ 40 * 371309 * 2
def baseEnd_371309 : Nat := 190659988340392985529887

theorem tailTrace_371309 : CollatzResearch.WordTrace tailWord_371309 prefixEnd_371309 190659988340392985529887 := by
  unfold tailWord_371309
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542751811818382373620981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9028501207878921582413987 13542751811818382373620981)
  ·
    refine ⟨1269632982357973347526967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13542751811818382373620981 1269632982357973347526967)
    ·
      refine ⟨1904449473536960021290451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269632982357973347526967 1904449473536960021290451)
      ·
        refine ⟨2856674210305440031935677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1904449473536960021290451 2856674210305440031935677)
        ·
          refine ⟨1071252828864540011975879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2856674210305440031935677 1071252828864540011975879)
          ·
            refine ⟨1606879243296810017963819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071252828864540011975879 1606879243296810017963819)
            ·
              refine ⟨2410318864945215026945729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606879243296810017963819 2410318864945215026945729)
              ·
                refine ⟨1807739148708911270209297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410318864945215026945729 1807739148708911270209297)
                ·
                  refine ⟨1355804361531683452656973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807739148708911270209297 1355804361531683452656973)
                  ·
                    refine ⟨508426635574381294746365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355804361531683452656973 508426635574381294746365)
                    ·
                      refine ⟨190659988340392985529887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 508426635574381294746365 190659988340392985529887)
                      ·
                        rfl

theorem cell23_371309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_371309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371309 prefixEnd_371309 := by exact prefixLift 371309
  have htrace : WordTrace (prefixWord ++ tailWord_371309) baseStart_371309 baseEnd_371309 := by
    simpa [prefixWord, tailWord_371309, baseEnd_371309] using wordTrace_append hprefix tailTrace_371309
  have hstable : (prefixWord ++ tailWord_371309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371309).length < 2 ^ (prefixWord ++ tailWord_371309).sum := by decide
  have hdescent : baseEnd_371309 < baseStart_371309 := by decide
  rcases family_descends (prefixWord ++ tailWord_371309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371310 : List Nat := [4, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_371310 : Nat := 118140960795 + 371310 * 2 ^ 59
def prefixEnd_371310 : Nat := 4983230072969 + 3 ^ 40 * 371310 * 2
def baseEnd_371310 : Nat := 190660501821047481617383

theorem tailTrace_371310 : CollatzResearch.WordTrace tailWord_371310 prefixEnd_371310 190660501821047481617383 := by
  unfold tailWord_371310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692848535601844943050923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9028525523209839696271589 1692848535601844943050923)
  ·
    refine ⟨2539272803402767414576385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692848535601844943050923 2539272803402767414576385)
    ·
      refine ⟨1904454602552075560932289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2539272803402767414576385 1904454602552075560932289)
      ·
        refine ⟨1428340951914056670699217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1904454602552075560932289 1428340951914056670699217)
        ·
          refine ⟨1071255713935542503024413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1428340951914056670699217 1071255713935542503024413)
          ·
            refine ⟨401720892725828438634155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1071255713935542503024413 401720892725828438634155)
            ·
              refine ⟨602581339088742657951233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401720892725828438634155 602581339088742657951233)
              ·
                refine ⟨451936004316556993463425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602581339088742657951233 451936004316556993463425)
                ·
                  refine ⟨338952003237417745097569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 451936004316556993463425 338952003237417745097569)
                  ·
                    refine ⟨254214002428063308823177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 338952003237417745097569 254214002428063308823177)
                    ·
                      refine ⟨190660501821047481617383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254214002428063308823177 190660501821047481617383)
                      ·
                        rfl

theorem cell23_371310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_371310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371310 prefixEnd_371310 := by exact prefixLift 371310
  have htrace : WordTrace (prefixWord ++ tailWord_371310) baseStart_371310 baseEnd_371310 := by
    simpa [prefixWord, tailWord_371310, baseEnd_371310] using wordTrace_append hprefix tailTrace_371310
  have hstable : (prefixWord ++ tailWord_371310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371310).length < 2 ^ (prefixWord ++ tailWord_371310).sum := by decide
  have hdescent : baseEnd_371310 < baseStart_371310 := by decide
  rcases family_descends (prefixWord ++ tailWord_371310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371342 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_371342 : Nat := 118140960795 + 371342 * 2 ^ 59
def prefixEnd_371342 : Nat := 4983230072969 + 3 ^ 40 * 371342 * 2
def baseEnd_371342 : Nat := 63558977733997118805745

theorem tailTrace_371342 : CollatzResearch.WordTrace tailWord_371342 prefixEnd_371342 63558977733997118805745 := by
  unfold tailWord_371342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692994427587353626196535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9029303613799219339714853 1692994427587353626196535)
  ·
    refine ⟨2539491641381030439294803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1692994427587353626196535 2539491641381030439294803)
    ·
      refine ⟨3809237462071545658942205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539491641381030439294803 3809237462071545658942205)
      ·
        refine ⟨1428464048276829622103327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3809237462071545658942205 1428464048276829622103327)
        ·
          refine ⟨2142696072415244433154991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428464048276829622103327 2142696072415244433154991)
          ·
            refine ⟨3214044108622866649732487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142696072415244433154991 3214044108622866649732487)
            ·
              refine ⟨4821066162934299974598731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214044108622866649732487 4821066162934299974598731)
              ·
                refine ⟨7231599244401449961898097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821066162934299974598731 7231599244401449961898097)
                ·
                  refine ⟨5423699433301087471423573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7231599244401449961898097 5423699433301087471423573)
                  ·
                    refine ⟨63558977733997118805745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5423699433301087471423573 63558977733997118805745)
                    ·
                      rfl

theorem cell23_371342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_371342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371342 prefixEnd_371342 := by exact prefixLift 371342
  have htrace : WordTrace (prefixWord ++ tailWord_371342) baseStart_371342 baseEnd_371342 := by
    simpa [prefixWord, tailWord_371342, baseEnd_371342] using wordTrace_append hprefix tailTrace_371342
  have hstable : (prefixWord ++ tailWord_371342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371342).length < 2 ^ (prefixWord ++ tailWord_371342).sum := by decide
  have hdescent : baseEnd_371342 < baseStart_371342 := by decide
  rcases family_descends (prefixWord ++ tailWord_371342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371389 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 6]
def baseStart_371389 : Nat := 118140960795 + 371389 * 2 ^ 59
def prefixEnd_371389 : Nat := 4983230072969 + 3 ^ 40 * 371389 * 2
def baseEnd_371389 : Nat := 21189007421416963614391

theorem tailTrace_371389 : CollatzResearch.WordTrace tailWord_371389 prefixEnd_371389 21189007421416963614391 := by
  unfold tailWord_371389
  simp only [CollatzResearch.WordTrace]
  refine ⟨13545669651528556036533221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9030446434352370691022147 13545669651528556036533221)
  ·
    refine ⟨2539813059661604256849979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13545669651528556036533221 2539813059661604256849979)
    ·
      refine ⟨3809719589492406385274969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539813059661604256849979 3809719589492406385274969)
      ·
        refine ⟨2857289692119304788956227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3809719589492406385274969 2857289692119304788956227)
        ·
          refine ⟨4285934538178957183434341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857289692119304788956227 4285934538178957183434341)
          ·
            refine ⟨803612725908554471893939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4285934538178957183434341 803612725908554471893939)
            ·
              refine ⟨1205419088862831707840909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803612725908554471893939 1205419088862831707840909)
              ·
                refine ⟨452032158323561890440341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1205419088862831707840909 452032158323561890440341)
                ·
                  refine ⟨21189007421416963614391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 452032158323561890440341 21189007421416963614391)
                  ·
                    rfl

theorem cell23_371389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_371389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371389 prefixEnd_371389 := by exact prefixLift 371389
  have htrace : WordTrace (prefixWord ++ tailWord_371389) baseStart_371389 baseEnd_371389 := by
    simpa [prefixWord, tailWord_371389, baseEnd_371389] using wordTrace_append hprefix tailTrace_371389
  have hstable : (prefixWord ++ tailWord_371389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371389).length < 2 ^ (prefixWord ++ tailWord_371389).sum := by decide
  have hdescent : baseEnd_371389 < baseStart_371389 := by decide
  rcases family_descends (prefixWord ++ tailWord_371389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371439 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_371439 : Nat := 118140960795 + 371439 * 2 ^ 59
def prefixEnd_371439 : Nat := 4983230072969 + 3 ^ 40 * 371439 * 2
def baseEnd_371439 : Nat := 190726740825477476904289

theorem tailTrace_371439 : CollatzResearch.WordTrace tailWord_371439 prefixEnd_371439 190726740825477476904289 := by
  unfold tailWord_371439
  simp only [CollatzResearch.WordTrace]
  refine ⟨13547493301347414575853371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9031662200898276383902247 13547493301347414575853371)
  ·
    refine ⟨20321239952021121863780057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13547493301347414575853371 20321239952021121863780057)
    ·
      refine ⟨15240929964015841397835043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20321239952021121863780057 15240929964015841397835043)
      ·
        refine ⟨22861394946023762096752565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15240929964015841397835043 22861394946023762096752565)
        ·
          refine ⟨2143255776189727696570553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22861394946023762096752565 2143255776189727696570553)
          ·
            refine ⟨1607441832142295772427915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2143255776189727696570553 1607441832142295772427915)
            ·
              refine ⟨2411162748213443658641873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607441832142295772427915 2411162748213443658641873)
              ·
                refine ⟨1808372061160082743981405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411162748213443658641873 1808372061160082743981405)
                ·
                  refine ⟨678139522935031028993027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1808372061160082743981405 678139522935031028993027)
                  ·
                    refine ⟨1017209284402546543489541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 678139522935031028993027 1017209284402546543489541)
                    ·
                      refine ⟨190726740825477476904289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1017209284402546543489541 190726740825477476904289)
                      ·
                        rfl

theorem cell23_371439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_371439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371439 prefixEnd_371439 := by exact prefixLift 371439
  have htrace : WordTrace (prefixWord ++ tailWord_371439) baseStart_371439 baseEnd_371439 := by
    simpa [prefixWord, tailWord_371439, baseEnd_371439] using wordTrace_append hprefix tailTrace_371439
  have hstable : (prefixWord ++ tailWord_371439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371439).length < 2 ^ (prefixWord ++ tailWord_371439).sum := by decide
  have hdescent : baseEnd_371439 < baseStart_371439 := by decide
  rcases family_descends (prefixWord ++ tailWord_371439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371479 : List Nat := [1, 1, 3, 4, 3, 1, 10]
def baseStart_371479 : Nat := 118140960795 + 371479 * 2 ^ 59
def prefixEnd_371479 : Nat := 4983230072969 + 3 ^ 40 * 371479 * 2
def baseEnd_371479 : Nat := 2354904691995769387705

theorem tailTrace_371479 : CollatzResearch.WordTrace tailWord_371479 prefixEnd_371479 2354904691995769387705 := by
  unfold tailWord_371479
  simp only [CollatzResearch.WordTrace]
  refine ⟨13548952221202501407309491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9032634814135000938206327 13548952221202501407309491)
  ·
    refine ⟨20323428331803752110964237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13548952221202501407309491 20323428331803752110964237)
    ·
      refine ⟨7621285624426407041611589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20323428331803752110964237 7621285624426407041611589)
      ·
        refine ⟨1428991054579951320302173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7621285624426407041611589 1428991054579951320302173)
        ·
          refine ⟨535871645467481745113315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1428991054579951320302173 535871645467481745113315)
          ·
            refine ⟨803807468201222617669973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535871645467481745113315 803807468201222617669973)
            ·
              refine ⟨2354904691995769387705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 803807468201222617669973 2354904691995769387705)
              ·
                rfl

theorem cell23_371479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 10].length) (baseStart_371479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371479 prefixEnd_371479 := by exact prefixLift 371479
  have htrace : WordTrace (prefixWord ++ tailWord_371479) baseStart_371479 baseEnd_371479 := by
    simpa [prefixWord, tailWord_371479, baseEnd_371479] using wordTrace_append hprefix tailTrace_371479
  have hstable : (prefixWord ++ tailWord_371479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371479).length < 2 ^ (prefixWord ++ tailWord_371479).sum := by decide
  have hdescent : baseEnd_371479 < baseStart_371479 := by decide
  rcases family_descends (prefixWord ++ tailWord_371479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371490 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_371490 : Nat := 118140960795 + 371490 * 2 ^ 59
def prefixEnd_371490 : Nat := 4983230072969 + 3 ^ 40 * 371490 * 2
def baseEnd_371490 : Nat := 190752928338856777366555

theorem tailTrace_371490 : CollatzResearch.WordTrace tailWord_371490 prefixEnd_371490 190752928338856777366555 := by
  unfold tailWord_371490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387338356040662571489981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9032902282775100190639949 3387338356040662571489981)
  ·
    refine ⟨1270251883515248464308743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3387338356040662571489981 1270251883515248464308743)
    ·
      refine ⟨1905377825272872696463115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1270251883515248464308743 1905377825272872696463115)
      ·
        refine ⟨2858066737909309044694673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905377825272872696463115 2858066737909309044694673)
        ·
          refine ⟨2143550053431981783521005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858066737909309044694673 2143550053431981783521005)
          ·
            refine ⟨803831270036993168820377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2143550053431981783521005 803831270036993168820377)
            ·
              refine ⟨602873452527744876615283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803831270036993168820377 602873452527744876615283)
              ·
                refine ⟨904310178791617314922925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602873452527744876615283 904310178791617314922925)
                ·
                  refine ⟨339116317046856493096097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904310178791617314922925 339116317046856493096097)
                  ·
                    refine ⟨254337237785142369822073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 339116317046856493096097 254337237785142369822073)
                    ·
                      refine ⟨190752928338856777366555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254337237785142369822073 190752928338856777366555)
                      ·
                        rfl

theorem cell23_371490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_371490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371490 prefixEnd_371490 := by exact prefixLift 371490
  have htrace : WordTrace (prefixWord ++ tailWord_371490) baseStart_371490 baseEnd_371490 := by
    simpa [prefixWord, tailWord_371490, baseEnd_371490] using wordTrace_append hprefix tailTrace_371490
  have hstable : (prefixWord ++ tailWord_371490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371490).length < 2 ^ (prefixWord ++ tailWord_371490).sum := by decide
  have hdescent : baseEnd_371490 < baseStart_371490 := by decide
  rcases family_descends (prefixWord ++ tailWord_371490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371519 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_371519 : Nat := 118140960795 + 371519 * 2 ^ 59
def prefixEnd_371519 : Nat := 4983230072969 + 3 ^ 40 * 371519 * 2
def baseEnd_371519 : Nat := 190767819277837163903921

theorem tailTrace_371519 : CollatzResearch.WordTrace tailWord_371519 prefixEnd_371519 190767819277837163903921 := by
  unfold tailWord_371519
  simp only [CollatzResearch.WordTrace]
  refine ⟨13550411141057588238765611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9033607427371725492510407 13550411141057588238765611)
  ·
    refine ⟨20325616711586382358148417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13550411141057588238765611 20325616711586382358148417)
    ·
      refine ⟨15244212533689786768611313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20325616711586382358148417 15244212533689786768611313)
      ·
        refine ⟨11433159400267340076458485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15244212533689786768611313 11433159400267340076458485)
        ·
          refine ⟨1071858693775063132167983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11433159400267340076458485 1071858693775063132167983)
          ·
            refine ⟨1607788040662594698251975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071858693775063132167983 1607788040662594698251975)
            ·
              refine ⟨2411682060993892047377963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607788040662594698251975 2411682060993892047377963)
              ·
                refine ⟨3617523091490838071066945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411682060993892047377963 3617523091490838071066945)
                ·
                  refine ⟨2713142318618128553300209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3617523091490838071066945 2713142318618128553300209)
                  ·
                    refine ⟨2034856738963596414975157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2713142318618128553300209 2034856738963596414975157)
                    ·
                      refine ⟨190767819277837163903921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2034856738963596414975157 190767819277837163903921)
                      ·
                        rfl

theorem cell23_371519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_371519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371519 prefixEnd_371519 := by exact prefixLift 371519
  have htrace : WordTrace (prefixWord ++ tailWord_371519) baseStart_371519 baseEnd_371519 := by
    simpa [prefixWord, tailWord_371519, baseEnd_371519] using wordTrace_append hprefix tailTrace_371519
  have hstable : (prefixWord ++ tailWord_371519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371519).length < 2 ^ (prefixWord ++ tailWord_371519).sum := by decide
  have hdescent : baseEnd_371519 < baseStart_371519 := by decide
  rcases family_descends (prefixWord ++ tailWord_371519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371654 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_371654 : Nat := 118140960795 + 371654 * 2 ^ 59
def prefixEnd_371654 : Nat := 4983230072969 + 3 ^ 40 * 371654 * 2
def baseEnd_371654 : Nat := 21204126574021570635089

theorem tailTrace_371654 : CollatzResearch.WordTrace tailWord_371654 prefixEnd_371654 21204126574021570635089 := by
  unfold tailWord_371654
  simp only [CollatzResearch.WordTrace]
  refine ⟨423604218611515821716563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9036889997045670863286677 423604218611515821716563)
  ·
    refine ⟨635406327917273732574845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 423604218611515821716563 635406327917273732574845)
    ·
      refine ⟨238277372968977649715567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 635406327917273732574845 238277372968977649715567)
      ·
        refine ⟨357416059453466474573351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238277372968977649715567 357416059453466474573351)
        ·
          refine ⟨536124089180199711860027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357416059453466474573351 536124089180199711860027)
          ·
            refine ⟨804186133770299567790041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536124089180199711860027 804186133770299567790041)
            ·
              refine ⟨603139600327724675842531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804186133770299567790041 603139600327724675842531)
              ·
                refine ⟨904709400491587013763797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603139600327724675842531 904709400491587013763797)
                ·
                  refine ⟨21204126574021570635089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 904709400491587013763797 21204126574021570635089)
                  ·
                    rfl

theorem cell23_371654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_371654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371654 prefixEnd_371654 := by exact prefixLift 371654
  have htrace : WordTrace (prefixWord ++ tailWord_371654) baseStart_371654 baseEnd_371654 := by
    simpa [prefixWord, tailWord_371654, baseEnd_371654] using wordTrace_append hprefix tailTrace_371654
  have hstable : (prefixWord ++ tailWord_371654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371654).length < 2 ^ (prefixWord ++ tailWord_371654).sum := by decide
  have hdescent : baseEnd_371654 < baseStart_371654 := by decide
  rcases family_descends (prefixWord ++ tailWord_371654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371663 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 3, 4]
def baseStart_371663 : Nat := 118140960795 + 371663 * 2 ^ 59
def prefixEnd_371663 : Nat := 4983230072969 + 3 ^ 40 * 371663 * 2
def baseEnd_371663 : Nat := 63613920164028200167753

theorem tailTrace_371663 : CollatzResearch.WordTrace tailWord_371663 prefixEnd_371663 63613920164028200167753 := by
  unfold tailWord_371663
  simp only [CollatzResearch.WordTrace]
  refine ⟨13555663252535900832007643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9037108835023933888005095 13555663252535900832007643)
  ·
    refine ⟨20333494878803851248011465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13555663252535900832007643 20333494878803851248011465)
    ·
      refine ⟨15250121159102888436008599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20333494878803851248011465 15250121159102888436008599)
      ·
        refine ⟨22875181738654332654012899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15250121159102888436008599 22875181738654332654012899)
        ·
          refine ⟨34312772607981498981019349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22875181738654332654012899 34312772607981498981019349)
          ·
            refine ⟨804205607999566382367641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 34312772607981498981019349 804205607999566382367641)
            ·
              refine ⟨603154205999674786775731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804205607999566382367641 603154205999674786775731)
              ·
                refine ⟨904731308999512180163597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603154205999674786775731 904731308999512180163597)
                ·
                  refine ⟨339274240874817067561349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904731308999512180163597 339274240874817067561349)
                  ·
                    refine ⟨63613920164028200167753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 339274240874817067561349 63613920164028200167753)
                    ·
                      rfl

theorem cell23_371663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_371663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371663 prefixEnd_371663 := by exact prefixLift 371663
  have htrace : WordTrace (prefixWord ++ tailWord_371663) baseStart_371663 baseEnd_371663 := by
    simpa [prefixWord, tailWord_371663, baseEnd_371663] using wordTrace_append hprefix tailTrace_371663
  have hstable : (prefixWord ++ tailWord_371663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371663).length < 2 ^ (prefixWord ++ tailWord_371663).sum := by decide
  have hdescent : baseEnd_371663 < baseStart_371663 := by decide
  rcases family_descends (prefixWord ++ tailWord_371663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371689 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 9]
def baseStart_371689 : Nat := 118140960795 + 371689 * 2 ^ 59
def prefixEnd_371689 : Nat := 4983230072969 + 3 ^ 40 * 371689 * 2
def baseEnd_371689 : Nat := 63618370329700499592713

theorem tailTrace_371689 : CollatzResearch.WordTrace tailWord_371689 prefixEnd_371689 63618370329700499592713 := by
  unfold tailWord_371689
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556611550441707272454121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9037741033627804848302747 13556611550441707272454121)
  ·
    refine ⟨10167458662831280454340591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13556611550441707272454121 10167458662831280454340591)
    ·
      refine ⟨15251187994246920681510887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10167458662831280454340591 15251187994246920681510887)
      ·
        refine ⟨22876781991370381022266331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15251187994246920681510887 22876781991370381022266331)
        ·
          refine ⟨34315172987055571533399497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22876781991370381022266331 34315172987055571533399497)
          ·
            refine ⟨25736379740291678650049623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34315172987055571533399497 25736379740291678650049623)
            ·
              refine ⟨38604569610437517975074435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25736379740291678650049623 38604569610437517975074435)
              ·
                refine ⟨57906854415656276962611653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38604569610437517975074435 57906854415656276962611653)
                ·
                  refine ⟨10857535202935551930489685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57906854415656276962611653 10857535202935551930489685)
                  ·
                    refine ⟨63618370329700499592713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 10857535202935551930489685 63618370329700499592713)
                    ·
                      rfl

theorem cell23_371689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_371689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371689 prefixEnd_371689 := by exact prefixLift 371689
  have htrace : WordTrace (prefixWord ++ tailWord_371689) baseStart_371689 baseEnd_371689 := by
    simpa [prefixWord, tailWord_371689, baseEnd_371689] using wordTrace_append hprefix tailTrace_371689
  have hstable : (prefixWord ++ tailWord_371689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371689).length < 2 ^ (prefixWord ++ tailWord_371689).sum := by decide
  have hdescent : baseEnd_371689 < baseStart_371689 := by decide
  rcases family_descends (prefixWord ++ tailWord_371689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371697 : List Nat := [1, 2, 2, 2, 4, 3, 1, 3, 1, 4]
def baseStart_371697 : Nat := 118140960795 + 371697 * 2 ^ 59
def prefixEnd_371697 : Nat := 4983230072969 + 3 ^ 40 * 371697 * 2
def baseEnd_371697 : Nat := 63619739611445822492701

theorem tailTrace_371697 : CollatzResearch.WordTrace tailWord_371697 prefixEnd_371697 63619739611445822492701 := by
  unfold tailWord_371697
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556903334412724638745345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9037935556275149759163563 13556903334412724638745345)
  ·
    refine ⟨10167677500809543479059009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13556903334412724638745345 10167677500809543479059009)
    ·
      refine ⟨7625758125607157609294257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10167677500809543479059009 7625758125607157609294257)
      ·
        refine ⟨5719318594205368206970693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7625758125607157609294257 5719318594205368206970693)
        ·
          refine ⟨1072372236413506538807005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5719318594205368206970693 1072372236413506538807005)
          ·
            refine ⟨402139588655064952052627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1072372236413506538807005 402139588655064952052627)
            ·
              refine ⟨603209382982597428078941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402139588655064952052627 603209382982597428078941)
              ·
                refine ⟨226203518618474035529603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 603209382982597428078941 226203518618474035529603)
                ·
                  refine ⟨339305277927711053294405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226203518618474035529603 339305277927711053294405)
                  ·
                    refine ⟨63619739611445822492701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 339305277927711053294405 63619739611445822492701)
                    ·
                      rfl

theorem cell23_371697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_371697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371697 prefixEnd_371697 := by exact prefixLift 371697
  have htrace : WordTrace (prefixWord ++ tailWord_371697) baseStart_371697 baseEnd_371697 := by
    simpa [prefixWord, tailWord_371697, baseEnd_371697] using wordTrace_append hprefix tailTrace_371697
  have hstable : (prefixWord ++ tailWord_371697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371697).length < 2 ^ (prefixWord ++ tailWord_371697).sum := by decide
  have hdescent : baseEnd_371697 < baseStart_371697 := by decide
  rcases family_descends (prefixWord ++ tailWord_371697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371714 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_371714 : Nat := 118140960795 + 371714 * 2 ^ 59
def prefixEnd_371714 : Nat := 4983230072969 + 3 ^ 40 * 371714 * 2
def baseEnd_371714 : Nat := 63622649335154633655175

theorem tailTrace_371714 : CollatzResearch.WordTrace tailWord_371714 prefixEnd_371714 63622649335154633655175 := by
  unfold tailWord_371714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389380843837784135528549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9038348916900757694742797 3389380843837784135528549)
  ·
    refine ⟨635508908219584525411603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3389380843837784135528549 635508908219584525411603)
    ·
      refine ⟨953263362329376788117405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635508908219584525411603 953263362329376788117405)
      ·
        refine ⟨357473760873516295544027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 953263362329376788117405 357473760873516295544027)
        ·
          refine ⟨536210641310274443316041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357473760873516295544027 536210641310274443316041)
          ·
            refine ⟨402157980982705832487031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536210641310274443316041 402157980982705832487031)
            ·
              refine ⟨603236971474058748730547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402157980982705832487031 603236971474058748730547)
              ·
                refine ⟨904855457211088123095821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603236971474058748730547 904855457211088123095821)
                ·
                  refine ⟨339320796454158046160933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904855457211088123095821 339320796454158046160933)
                  ·
                    refine ⟨63622649335154633655175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 339320796454158046160933 63622649335154633655175)
                    ·
                      rfl

theorem cell23_371714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_371714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371714 prefixEnd_371714 := by exact prefixLift 371714
  have htrace : WordTrace (prefixWord ++ tailWord_371714) baseStart_371714 baseEnd_371714 := by
    simpa [prefixWord, tailWord_371714, baseEnd_371714] using wordTrace_append hprefix tailTrace_371714
  have hstable : (prefixWord ++ tailWord_371714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371714).length < 2 ^ (prefixWord ++ tailWord_371714).sum := by decide
  have hdescent : baseEnd_371714 < baseStart_371714 := by decide
  rcases family_descends (prefixWord ++ tailWord_371714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371720 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_371720 : Nat := 118140960795 + 371720 * 2 ^ 59
def prefixEnd_371720 : Nat := 4983230072969 + 3 ^ 40 * 371720 * 2
def baseEnd_371720 : Nat := 190871028889390877490497

theorem tailTrace_371720 : CollatzResearch.WordTrace tailWord_371720 prefixEnd_371720 190871028889390877490497 := by
  unfold tailWord_371720
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778871106664699783416307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9038494808886266377888409 6778871106664699783416307)
  ·
    refine ⟨10168306659997049675124461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6778871106664699783416307 10168306659997049675124461)
    ·
      refine ⟨3813114997498893628171673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10168306659997049675124461 3813114997498893628171673)
      ·
        refine ⟨2859836248124170221128755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813114997498893628171673 2859836248124170221128755)
        ·
          refine ⟨4289754372186255331693133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2859836248124170221128755 4289754372186255331693133)
          ·
            refine ⟨1608657889569845749384925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4289754372186255331693133 1608657889569845749384925)
            ·
              refine ⟨603246708588692156019347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1608657889569845749384925 603246708588692156019347)
              ·
                refine ⟨904870062883038234029021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603246708588692156019347 904870062883038234029021)
                ·
                  refine ⟨339326273581139337760883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 904870062883038234029021 339326273581139337760883)
                  ·
                    refine ⟨508989410371709006641325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 339326273581139337760883 508989410371709006641325)
                    ·
                      refine ⟨190871028889390877490497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 508989410371709006641325 190871028889390877490497)
                      ·
                        rfl

theorem cell23_371720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_371720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371720 prefixEnd_371720 := by exact prefixLift 371720
  have htrace : WordTrace (prefixWord ++ tailWord_371720) baseStart_371720 baseEnd_371720 := by
    simpa [prefixWord, tailWord_371720, baseEnd_371720] using wordTrace_append hprefix tailTrace_371720
  have hstable : (prefixWord ++ tailWord_371720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371720).length < 2 ^ (prefixWord ++ tailWord_371720).sum := by decide
  have hdescent : baseEnd_371720 < baseStart_371720 := by decide
  rcases family_descends (prefixWord ++ tailWord_371720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371743 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_371743 : Nat := 118140960795 + 371743 * 2 ^ 59
def prefixEnd_371743 : Nat := 4983230072969 + 3 ^ 40 * 371743 * 2
def baseEnd_371743 : Nat := 190882838944444287502891

theorem tailTrace_371743 : CollatzResearch.WordTrace tailWord_371743 prefixEnd_371743 190882838944444287502891 := by
  unfold tailWord_371743
  simp only [CollatzResearch.WordTrace]
  refine ⟨13558581092246074494919883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9039054061497382996613255 13558581092246074494919883)
  ·
    refine ⟨20337871638369111742379825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13558581092246074494919883 20337871638369111742379825)
    ·
      refine ⟨15253403728776833806784869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20337871638369111742379825 15253403728776833806784869)
      ·
        refine ⟨2860013199145656338772163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15253403728776833806784869 2860013199145656338772163)
        ·
          refine ⟨4290019798718484508158245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860013199145656338772163 4290019798718484508158245)
          ·
            refine ⟨804378712259715845279671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4290019798718484508158245 804378712259715845279671)
            ·
              refine ⟨1206568068389573767919507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 804378712259715845279671 1206568068389573767919507)
              ·
                refine ⟨1809852102584360651879261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206568068389573767919507 1809852102584360651879261)
                ·
                  refine ⟨678694538469135244454723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1809852102584360651879261 678694538469135244454723)
                  ·
                    refine ⟨1018041807703702866682085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 678694538469135244454723 1018041807703702866682085)
                    ·
                      refine ⟨190882838944444287502891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1018041807703702866682085 190882838944444287502891)
                      ·
                        rfl

theorem cell23_371743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_371743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371743 prefixEnd_371743 := by exact prefixLift 371743
  have htrace : WordTrace (prefixWord ++ tailWord_371743) baseStart_371743 baseEnd_371743 := by
    simpa [prefixWord, tailWord_371743, baseEnd_371743] using wordTrace_append hprefix tailTrace_371743
  have hstable : (prefixWord ++ tailWord_371743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371743).length < 2 ^ (prefixWord ++ tailWord_371743).sum := by decide
  have hdescent : baseEnd_371743 < baseStart_371743 := by decide
  rcases family_descends (prefixWord ++ tailWord_371743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371760 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 1, 1, 4]
def baseStart_371760 : Nat := 118140960795 + 371760 * 2 ^ 59
def prefixEnd_371760 : Nat := 4983230072969 + 3 ^ 40 * 371760 * 2
def baseEnd_371760 : Nat := 190891568115570720990313

theorem tailTrace_371760 : CollatzResearch.WordTrace tailWord_371760 prefixEnd_371760 190891568115570720990313 := by
  unfold tailWord_371760
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779600566592243199144367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9039467422122990932192489 6779600566592243199144367)
  ·
    refine ⟨10169400849888364798716551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6779600566592243199144367 10169400849888364798716551)
    ·
      refine ⟨15254101274832547198074827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10169400849888364798716551 15254101274832547198074827)
      ·
        refine ⟨22881151912248820797112241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15254101274832547198074827 22881151912248820797112241)
        ·
          refine ⟨17160863934186615597834181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22881151912248820797112241 17160863934186615597834181)
          ·
            refine ⟨3217661987659990424593909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17160863934186615597834181 3217661987659990424593909)
            ·
              refine ⟨301655811343124102305679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3217661987659990424593909 301655811343124102305679)
              ·
                refine ⟨452483717014686153458519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301655811343124102305679 452483717014686153458519)
                ·
                  refine ⟨678725575522029230187779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452483717014686153458519 678725575522029230187779)
                  ·
                    refine ⟨1018088363283043845281669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 678725575522029230187779 1018088363283043845281669)
                    ·
                      refine ⟨190891568115570720990313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1018088363283043845281669 190891568115570720990313)
                      ·
                        rfl

theorem cell23_371760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 1, 1, 4].length) (baseStart_371760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371760 prefixEnd_371760 := by exact prefixLift 371760
  have htrace : WordTrace (prefixWord ++ tailWord_371760) baseStart_371760 baseEnd_371760 := by
    simpa [prefixWord, tailWord_371760, baseEnd_371760] using wordTrace_append hprefix tailTrace_371760
  have hstable : (prefixWord ++ tailWord_371760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371760).length < 2 ^ (prefixWord ++ tailWord_371760).sum := by decide
  have hdescent : baseEnd_371760 < baseStart_371760 := by decide
  rcases family_descends (prefixWord ++ tailWord_371760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371783 : List Nat := [1, 1, 4, 1, 3, 4, 1, 8]
def baseStart_371783 : Nat := 118140960795 + 371783 * 2 ^ 59
def prefixEnd_371783 : Nat := 4983230072969 + 3 ^ 40 * 371783 * 2
def baseEnd_371783 : Nat := 7070495487800893740841

theorem tailTrace_371783 : CollatzResearch.WordTrace tailWord_371783 prefixEnd_371783 7070495487800893740841 := by
  unfold tailWord_371783
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560040012101161326376003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9040026674734107550917335 13560040012101161326376003)
  ·
    refine ⟨20340060018151741989564005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13560040012101161326376003 20340060018151741989564005)
    ·
      refine ⟨3813761253403451623043251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20340060018151741989564005 3813761253403451623043251)
      ·
        refine ⟨5720641880105177434564877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813761253403451623043251 5720641880105177434564877)
        ·
          refine ⟨2145240705039441537961829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5720641880105177434564877 2145240705039441537961829)
          ·
            refine ⟨402232632194895288367843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2145240705039441537961829 402232632194895288367843)
            ·
              refine ⟨603348948292342932551765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402232632194895288367843 603348948292342932551765)
              ·
                refine ⟨7070495487800893740841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 603348948292342932551765 7070495487800893740841)
                ·
                  rfl

theorem cell23_371783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 8].length) (baseStart_371783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371783 prefixEnd_371783 := by exact prefixLift 371783
  have htrace : WordTrace (prefixWord ++ tailWord_371783) baseStart_371783 baseEnd_371783 := by
    simpa [prefixWord, tailWord_371783, baseEnd_371783] using wordTrace_append hprefix tailTrace_371783
  have hstable : (prefixWord ++ tailWord_371783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371783).length < 2 ^ (prefixWord ++ tailWord_371783).sum := by decide
  have hdescent : baseEnd_371783 < baseStart_371783 := by decide
  rcases family_descends (prefixWord ++ tailWord_371783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371786 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_371786 : Nat := 118140960795 + 371786 * 2 ^ 59
def prefixEnd_371786 : Nat := 4983230072969 + 3 ^ 40 * 371786 * 2
def baseEnd_371786 : Nat := 190904918612587619265193

theorem tailTrace_371786 : CollatzResearch.WordTrace tailWord_371786 prefixEnd_371786 190904918612587619265193 := by
  unfold tailWord_371786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390037357772573209683803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9040099620726861892490141 3390037357772573209683803)
  ·
    refine ⟨5085056036658859814525705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3390037357772573209683803 5085056036658859814525705)
    ·
      refine ⟨3813792027494144860894279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5085056036658859814525705 3813792027494144860894279)
      ·
        refine ⟨5720688041241217291341419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813792027494144860894279 5720688041241217291341419)
        ·
          refine ⟨8581032061861825937012129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5720688041241217291341419 8581032061861825937012129)
          ·
            refine ⟨6435774046396369452759097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8581032061861825937012129 6435774046396369452759097)
            ·
              refine ⟨4826830534797277089569323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6435774046396369452759097 4826830534797277089569323)
              ·
                refine ⟨7240245802195915634353985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826830534797277089569323 7240245802195915634353985)
                ·
                  refine ⟨5430184351646936725765489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7240245802195915634353985 5430184351646936725765489)
                  ·
                    refine ⟨4072638263735202544324117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5430184351646936725765489 4072638263735202544324117)
                    ·
                      refine ⟨190904918612587619265193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4072638263735202544324117 190904918612587619265193)
                      ·
                        rfl

theorem cell23_371786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_371786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371786 prefixEnd_371786 := by exact prefixLift 371786
  have htrace : WordTrace (prefixWord ++ tailWord_371786) baseStart_371786 baseEnd_371786 := by
    simpa [prefixWord, tailWord_371786, baseEnd_371786] using wordTrace_append hprefix tailTrace_371786
  have hstable : (prefixWord ++ tailWord_371786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371786).length < 2 ^ (prefixWord ++ tailWord_371786).sum := by decide
  have hdescent : baseEnd_371786 < baseStart_371786 := by decide
  rcases family_descends (prefixWord ++ tailWord_371786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371793 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_371793 : Nat := 118140960795 + 371793 * 2 ^ 59
def prefixEnd_371793 : Nat := 4983230072969 + 3 ^ 40 * 371793 * 2
def baseEnd_371793 : Nat := 190908512977169091877661

theorem tailTrace_371793 : CollatzResearch.WordTrace tailWord_371793 prefixEnd_371793 190908512977169091877661 := by
  unfold tailWord_371793
  simp only [CollatzResearch.WordTrace]
  refine ⟨13560404742064933034240033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9040269828043288689493355 13560404742064933034240033)
  ·
    refine ⟨10170303556548699775680025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13560404742064933034240033 10170303556548699775680025)
    ·
      refine ⟨7627727667411524831760019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10170303556548699775680025 7627727667411524831760019)
      ·
        refine ⟨11441591501117287247640029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7627727667411524831760019 11441591501117287247640029)
        ·
          refine ⟨4290596812918982717865011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11441591501117287247640029 4290596812918982717865011)
          ·
            refine ⟨6435895219378474076797517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290596812918982717865011 6435895219378474076797517)
            ·
              refine ⟨2413460707266927778799069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6435895219378474076797517 2413460707266927778799069)
              ·
                refine ⟨905047765225097917049651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413460707266927778799069 905047765225097917049651)
                ·
                  refine ⟨1357571647837646875574477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905047765225097917049651 1357571647837646875574477)
                  ·
                    refine ⟨509089367939117578340429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357571647837646875574477 509089367939117578340429)
                    ·
                      refine ⟨190908512977169091877661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 509089367939117578340429 190908512977169091877661)
                      ·
                        rfl

theorem cell23_371793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_371793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371793 prefixEnd_371793 := by exact prefixLift 371793
  have htrace : WordTrace (prefixWord ++ tailWord_371793) baseStart_371793 baseEnd_371793 := by
    simpa [prefixWord, tailWord_371793, baseEnd_371793] using wordTrace_append hprefix tailTrace_371793
  have hstable : (prefixWord ++ tailWord_371793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371793).length < 2 ^ (prefixWord ++ tailWord_371793).sum := by decide
  have hdescent : baseEnd_371793 < baseStart_371793 := by decide
  rcases family_descends (prefixWord ++ tailWord_371793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371798 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_371798 : Nat := 118140960795 + 371798 * 2 ^ 59
def prefixEnd_371798 : Nat := 4983230072969 + 3 ^ 40 * 371798 * 2
def baseEnd_371798 : Nat := 190911080380441572315139

theorem tailTrace_371798 : CollatzResearch.WordTrace tailWord_371798 prefixEnd_371798 190911080380441572315139 := by
  unfold tailWord_371798
  simp only [CollatzResearch.WordTrace]
  refine ⟨847536694190426180510753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9040391404697879258781365 847536694190426180510753)
  ·
    refine ⟨635652520642819635383065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 847536694190426180510753 635652520642819635383065)
    ·
      refine ⟨476739390482114726537299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 635652520642819635383065 476739390482114726537299)
      ·
        refine ⟨715109085723172089805949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476739390482114726537299 715109085723172089805949)
        ·
          refine ⟨268165907146189533677231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 715109085723172089805949 268165907146189533677231)
          ·
            refine ⟨402248860719284300515847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268165907146189533677231 402248860719284300515847)
            ·
              refine ⟨603373291078926450773771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402248860719284300515847 603373291078926450773771)
              ·
                refine ⟨905059936618389676160657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603373291078926450773771 905059936618389676160657)
                ·
                  refine ⟨678794952463792257120493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905059936618389676160657 678794952463792257120493)
                  ·
                    refine ⟨254548107173922096420185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678794952463792257120493 254548107173922096420185)
                    ·
                      refine ⟨190911080380441572315139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254548107173922096420185 190911080380441572315139)
                      ·
                        rfl

theorem cell23_371798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_371798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371798 prefixEnd_371798 := by exact prefixLift 371798
  have htrace : WordTrace (prefixWord ++ tailWord_371798) baseStart_371798 baseEnd_371798 := by
    simpa [prefixWord, tailWord_371798, baseEnd_371798] using wordTrace_append hprefix tailTrace_371798
  have hstable : (prefixWord ++ tailWord_371798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371798).length < 2 ^ (prefixWord ++ tailWord_371798).sum := by decide
  have hdescent : baseEnd_371798 < baseStart_371798 := by decide
  rcases family_descends (prefixWord ++ tailWord_371798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371838 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_371838 : Nat := 118140960795 + 371838 * 2 ^ 59
def prefixEnd_371838 : Nat := 4983230072969 + 3 ^ 40 * 371838 * 2
def baseEnd_371838 : Nat := 63643873202207138604985

theorem tailTrace_371838 : CollatzResearch.WordTrace tailWord_371838 prefixEnd_371838 63643873202207138604985 := by
  unfold tailWord_371838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695255753362738214953521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9041364017934603813085445 1695255753362738214953521)
  ·
    refine ⟨1271441815022053661215141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1695255753362738214953521 1271441815022053661215141)
    ·
      refine ⟨238395340316635061477839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1271441815022053661215141 238395340316635061477839)
      ·
        refine ⟨357593010474952592216759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238395340316635061477839 357593010474952592216759)
        ·
          refine ⟨536389515712428888325139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357593010474952592216759 536389515712428888325139)
          ·
            refine ⟨804584273568643332487709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536389515712428888325139 804584273568643332487709)
            ·
              refine ⟨301719102588241249682891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 804584273568643332487709 301719102588241249682891)
              ·
                refine ⟨452578653882361874524337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301719102588241249682891 452578653882361874524337)
                ·
                  refine ⟨339433990411771405893253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452578653882361874524337 339433990411771405893253)
                  ·
                    refine ⟨63643873202207138604985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 339433990411771405893253 63643873202207138604985)
                    ·
                      rfl

theorem cell23_371838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_371838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371838 prefixEnd_371838 := by exact prefixLift 371838
  have htrace : WordTrace (prefixWord ++ tailWord_371838) baseStart_371838 baseEnd_371838 := by
    simpa [prefixWord, tailWord_371838, baseEnd_371838] using wordTrace_append hprefix tailTrace_371838
  have hstable : (prefixWord ++ tailWord_371838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371838).length < 2 ^ (prefixWord ++ tailWord_371838).sum := by decide
  have hdescent : baseEnd_371838 < baseStart_371838 := by decide
  rcases family_descends (prefixWord ++ tailWord_371838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371844 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_371844 : Nat := 118140960795 + 371844 * 2 ^ 59
def prefixEnd_371844 : Nat := 4983230072969 + 3 ^ 40 * 371844 * 2
def baseEnd_371844 : Nat := 190934700490548392339927

theorem tailTrace_371844 : CollatzResearch.WordTrace tailWord_371844 prefixEnd_371844 190934700490548392339927 := by
  unfold tailWord_371844
  simp only [CollatzResearch.WordTrace]
  refine ⟨6781132432440084372173293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9041509909920112496231057 6781132432440084372173293)
  ·
    refine ⟨2542924662165031639564985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6781132432440084372173293 2542924662165031639564985)
    ·
      refine ⟨1907193496623773729673739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2542924662165031639564985 1907193496623773729673739)
      ·
        refine ⟨2860790244935660594510609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907193496623773729673739 2860790244935660594510609)
        ·
          refine ⟨2145592683701745445882957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2860790244935660594510609 2145592683701745445882957)
          ·
            refine ⟨804597256388154542206109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2145592683701745445882957 804597256388154542206109)
            ·
              refine ⟨301723971145557953327291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 804597256388154542206109 301723971145557953327291)
              ·
                refine ⟨452585956718336929990937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301723971145557953327291 452585956718336929990937)
                ·
                  refine ⟨339439467538752697493203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452585956718336929990937 339439467538752697493203)
                  ·
                    refine ⟨509159201308129046239805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 339439467538752697493203 509159201308129046239805)
                    ·
                      refine ⟨190934700490548392339927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 509159201308129046239805 190934700490548392339927)
                      ·
                        rfl

theorem cell23_371844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_371844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371844 prefixEnd_371844 := by exact prefixLift 371844
  have htrace : WordTrace (prefixWord ++ tailWord_371844) baseStart_371844 baseEnd_371844 := by
    simpa [prefixWord, tailWord_371844, baseEnd_371844] using wordTrace_append hprefix tailTrace_371844
  have hstable : (prefixWord ++ tailWord_371844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371844).length < 2 ^ (prefixWord ++ tailWord_371844).sum := by decide
  have hdescent : baseEnd_371844 < baseStart_371844 := by decide
  rcases family_descends (prefixWord ++ tailWord_371844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371854 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_371854 : Nat := 118140960795 + 371854 * 2 ^ 59
def prefixEnd_371854 : Nat := 4983230072969 + 3 ^ 40 * 371854 * 2
def baseEnd_371854 : Nat := 190939835297093353214881

theorem tailTrace_371854 : CollatzResearch.WordTrace tailWord_371854 prefixEnd_371854 190939835297093353214881 := by
  unfold tailWord_371854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695328699355492556526327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9041753063229293634807077 1695328699355492556526327)
  ·
    refine ⟨2542993049033238834789491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1695328699355492556526327 2542993049033238834789491)
    ·
      refine ⟨3814489573549858252184237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542993049033238834789491 3814489573549858252184237)
      ·
        refine ⟨1430433590081196844569089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3814489573549858252184237 1430433590081196844569089)
        ·
          refine ⟨1072825192560897633426817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430433590081196844569089 1072825192560897633426817)
          ·
            refine ⟨804618894420673225070113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1072825192560897633426817 804618894420673225070113)
            ·
              refine ⟨603464170815504918802585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804618894420673225070113 603464170815504918802585)
              ·
                refine ⟨452598128111628689101939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603464170815504918802585 452598128111628689101939)
                ·
                  refine ⟨678897192167443033652909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452598128111628689101939 678897192167443033652909)
                  ·
                    refine ⟨254586447062791137619841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 678897192167443033652909 254586447062791137619841)
                    ·
                      refine ⟨190939835297093353214881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254586447062791137619841 190939835297093353214881)
                      ·
                        rfl

theorem cell23_371854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_371854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371854 prefixEnd_371854 := by exact prefixLift 371854
  have htrace : WordTrace (prefixWord ++ tailWord_371854) baseStart_371854 baseEnd_371854 := by
    simpa [prefixWord, tailWord_371854, baseEnd_371854] using wordTrace_append hprefix tailTrace_371854
  have hstable : (prefixWord ++ tailWord_371854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371854).length < 2 ^ (prefixWord ++ tailWord_371854).sum := by decide
  have hdescent : baseEnd_371854 < baseStart_371854 := by decide
  rcases family_descends (prefixWord ++ tailWord_371854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371856 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 9]
def baseStart_371856 : Nat := 118140960795 + 371856 * 2 ^ 59
def prefixEnd_371856 : Nat := 4983230072969 + 3 ^ 40 * 371856 * 2
def baseEnd_371856 : Nat := 21215651362044705043319

theorem tailTrace_371856 : CollatzResearch.WordTrace tailWord_371856 prefixEnd_371856 21215651362044705043319 := by
  unfold tailWord_371856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6781351270418347396891711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9041801693891129862522281 6781351270418347396891711)
  ·
    refine ⟨10172026905627521095337567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6781351270418347396891711 10172026905627521095337567)
    ·
      refine ⟨15258040358441281643006351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10172026905627521095337567 15258040358441281643006351)
      ·
        refine ⟨22887060537661922464509527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15258040358441281643006351 22887060537661922464509527)
        ·
          refine ⟨34330590806492883696764291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22887060537661922464509527 34330590806492883696764291)
          ·
            refine ⟨51495886209739325545146437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34330590806492883696764291 51495886209739325545146437)
            ·
              refine ⟨9655478664326123539714957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51495886209739325545146437 9655478664326123539714957)
              ·
                refine ⟨3620804499122296327393109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9655478664326123539714957 3620804499122296327393109)
                ·
                  refine ⟨21215651362044705043319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3620804499122296327393109 21215651362044705043319)
                  ·
                    rfl

theorem cell23_371856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_371856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371856 prefixEnd_371856 := by exact prefixLift 371856
  have htrace : WordTrace (prefixWord ++ tailWord_371856) baseStart_371856 baseEnd_371856 := by
    simpa [prefixWord, tailWord_371856, baseEnd_371856] using wordTrace_append hprefix tailTrace_371856
  have hstable : (prefixWord ++ tailWord_371856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371856).length < 2 ^ (prefixWord ++ tailWord_371856).sum := by decide
  have hdescent : baseEnd_371856 < baseStart_371856 := by decide
  rcases family_descends (prefixWord ++ tailWord_371856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371870 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_371870 : Nat := 118140960795 + 371870 * 2 ^ 59
def prefixEnd_371870 : Nat := 4983230072969 + 3 ^ 40 * 371870 * 2
def baseEnd_371870 : Nat := 190948050987565290614807

theorem tailTrace_371870 : CollatzResearch.WordTrace tailWord_371870 prefixEnd_371870 190948050987565290614807 := by
  unfold tailWord_371870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1695401645348246898099133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9042142108523983456528709 1695401645348246898099133)
  ·
    refine ⟨635775617005592586787175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1695401645348246898099133 635775617005592586787175)
    ·
      refine ⟨953663425508388880180763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 635775617005592586787175 953663425508388880180763)
      ·
        refine ⟨1430495138262583320271145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 953663425508388880180763 1430495138262583320271145)
        ·
          refine ⟨1072871353696937490203359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1430495138262583320271145 1072871353696937490203359)
          ·
            refine ⟨1609307030545406235305039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072871353696937490203359 1609307030545406235305039)
            ·
              refine ⟨2413960545818109352957559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609307030545406235305039 2413960545818109352957559)
              ·
                refine ⟨3620940818727164029436339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413960545818109352957559 3620940818727164029436339)
                ·
                  refine ⟨5431411228090746044154509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620940818727164029436339 5431411228090746044154509)
                  ·
                    refine ⟨2036779210534029766557941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5431411228090746044154509 2036779210534029766557941)
                    ·
                      refine ⟨190948050987565290614807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2036779210534029766557941 190948050987565290614807)
                      ·
                        rfl

theorem cell23_371870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_371870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371870 prefixEnd_371870 := by exact prefixLift 371870
  have htrace : WordTrace (prefixWord ++ tailWord_371870) baseStart_371870 baseEnd_371870 := by
    simpa [prefixWord, tailWord_371870, baseEnd_371870] using wordTrace_append hprefix tailTrace_371870
  have hstable : (prefixWord ++ tailWord_371870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371870).length < 2 ^ (prefixWord ++ tailWord_371870).sum := by decide
  have hdescent : baseEnd_371870 < baseStart_371870 := by decide
  rcases family_descends (prefixWord ++ tailWord_371870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371890 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 7]
def baseStart_371890 : Nat := 118140960795 + 371890 * 2 ^ 59
def prefixEnd_371890 : Nat := 4983230072969 + 3 ^ 40 * 371890 * 2
def baseEnd_371890 : Nat := 21217591177850579151635

theorem tailTrace_371890 : CollatzResearch.WordTrace tailWord_371890 prefixEnd_371890 21217591177850579151635 := by
  unfold tailWord_371890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390985655678379650130281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9042628415142345733680749 3390985655678379650130281)
  ·
    refine ⟨2543239241758784737597711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3390985655678379650130281 2543239241758784737597711)
    ·
      refine ⟨3814858862638177106396567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2543239241758784737597711 3814858862638177106396567)
      ·
        refine ⟨5722288293957265659594851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3814858862638177106396567 5722288293957265659594851)
        ·
          refine ⟨8583432440935898489392277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5722288293957265659594851 8583432440935898489392277)
          ·
            refine ⟨402348395668870241690263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8583432440935898489392277 402348395668870241690263)
            ·
              refine ⟨603522593503305362535395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402348395668870241690263 603522593503305362535395)
              ·
                refine ⟨905283890254958043803093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603522593503305362535395 905283890254958043803093)
                ·
                  refine ⟨21217591177850579151635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 905283890254958043803093 21217591177850579151635)
                  ·
                    rfl

theorem cell23_371890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_371890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371890 prefixEnd_371890 := by exact prefixLift 371890
  have htrace : WordTrace (prefixWord ++ tailWord_371890) baseStart_371890 baseEnd_371890 := by
    simpa [prefixWord, tailWord_371890, baseEnd_371890] using wordTrace_append hprefix tailTrace_371890
  have hstable : (prefixWord ++ tailWord_371890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371890).length < 2 ^ (prefixWord ++ tailWord_371890).sum := by decide
  have hdescent : baseEnd_371890 < baseStart_371890 := by decide
  rcases family_descends (prefixWord ++ tailWord_371890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371923 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 4]
def baseStart_371923 : Nat := 118140960795 + 371923 * 2 ^ 59
def prefixEnd_371923 : Nat := 4983230072969 + 3 ^ 40 * 371923 * 2
def baseEnd_371923 : Nat := 190975265462253583252063

theorem tailTrace_371923 : CollatzResearch.WordTrace tailWord_371923 prefixEnd_371923 190975265462253583252063 := by
  unfold tailWord_371923
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565146231593965236472423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9043430821062643490981615 13565146231593965236472423)
  ·
    refine ⟨20347719347390947854708635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13565146231593965236472423 20347719347390947854708635)
    ·
      refine ⟨30521579021086421782062953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20347719347390947854708635 30521579021086421782062953)
      ·
        refine ⟨22891184265814816336547215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30521579021086421782062953 22891184265814816336547215)
        ·
          refine ⟨34336776398722224504820823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22891184265814816336547215 34336776398722224504820823)
          ·
            refine ⟨51505164598083336757231235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34336776398722224504820823 51505164598083336757231235)
            ·
              refine ⟨77257746897125005135846853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51505164598083336757231235 77257746897125005135846853)
              ·
                refine ⟨14485827543210938462971285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77257746897125005135846853 14485827543210938462971285)
                ·
                  refine ⟨679023166088012740451779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14485827543210938462971285 679023166088012740451779)
                  ·
                    refine ⟨1018534749132019110677669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679023166088012740451779 1018534749132019110677669)
                    ·
                      refine ⟨190975265462253583252063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1018534749132019110677669 190975265462253583252063)
                      ·
                        rfl

theorem cell23_371923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_371923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371923 prefixEnd_371923 := by exact prefixLift 371923
  have htrace : WordTrace (prefixWord ++ tailWord_371923) baseStart_371923 baseEnd_371923 := by
    simpa [prefixWord, tailWord_371923, baseEnd_371923] using wordTrace_append hprefix tailTrace_371923
  have hstable : (prefixWord ++ tailWord_371923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371923).length < 2 ^ (prefixWord ++ tailWord_371923).sum := by decide
  have hdescent : baseEnd_371923 < baseStart_371923 := by decide
  rcases family_descends (prefixWord ++ tailWord_371923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371940 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_371940 : Nat := 118140960795 + 371940 * 2 ^ 59
def prefixEnd_371940 : Nat := 4983230072969 + 3 ^ 40 * 371940 * 2
def baseEnd_371940 : Nat := 190983994633380016739485

theorem tailTrace_371940 : CollatzResearch.WordTrace tailWord_371940 prefixEnd_371940 190983994633380016739485 := by
  unfold tailWord_371940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6782883136266188569920637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9043844181688251426560849 6782883136266188569920637)
  ·
    refine ⟨2543581176099820713720239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6782883136266188569920637 2543581176099820713720239)
    ·
      refine ⟨3815371764149731070580359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2543581176099820713720239 3815371764149731070580359)
      ·
        refine ⟨5723057646224596605870539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3815371764149731070580359 5723057646224596605870539)
        ·
          refine ⟨8584586469336894908805809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5723057646224596605870539 8584586469336894908805809)
          ·
            refine ⟨6438439852002671181604357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8584586469336894908805809 6438439852002671181604357)
            ·
              refine ⟨1207207472250500846550817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6438439852002671181604357 1207207472250500846550817)
              ·
                refine ⟨905405604187875634913113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207207472250500846550817 905405604187875634913113)
                ·
                  refine ⟨679054203140906726184835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905405604187875634913113 679054203140906726184835)
                  ·
                    refine ⟨1018581304711360089277253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679054203140906726184835 1018581304711360089277253)
                    ·
                      refine ⟨190983994633380016739485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1018581304711360089277253 190983994633380016739485)
                      ·
                        rfl

theorem cell23_371940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_371940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371940 prefixEnd_371940 := by exact prefixLift 371940
  have htrace : WordTrace (prefixWord ++ tailWord_371940) baseStart_371940 baseEnd_371940 := by
    simpa [prefixWord, tailWord_371940, baseEnd_371940] using wordTrace_append hprefix tailTrace_371940
  have hstable : (prefixWord ++ tailWord_371940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371940).length < 2 ^ (prefixWord ++ tailWord_371940).sum := by decide
  have hdescent : baseEnd_371940 < baseStart_371940 := by decide
  rcases family_descends (prefixWord ++ tailWord_371940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371941 : List Nat := [1, 3, 1, 4, 4, 1, 2, 2, 5]
def baseStart_371941 : Nat := 118140960795 + 371941 * 2 ^ 59
def prefixEnd_371941 : Nat := 4983230072969 + 3 ^ 40 * 371941 * 2
def baseEnd_371941 : Nat := 21220500901559390314109

theorem tailTrace_371941 : CollatzResearch.WordTrace tailWord_371941 prefixEnd_371941 21220500901559390314109 := by
  unfold tailWord_371941
  simp only [CollatzResearch.WordTrace]
  refine ⟨13565802745528754310627677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9043868497019169540418451 13565802745528754310627677)
  ·
    refine ⟨5087176029573282866485379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13565802745528754310627677 5087176029573282866485379)
    ·
      refine ⟨7630764044359924299728069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5087176029573282866485379 7630764044359924299728069)
      ·
        refine ⟨1430768258317485806199013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7630764044359924299728069 1430768258317485806199013)
        ·
          refine ⟨268269048434528588662315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1430768258317485806199013 268269048434528588662315)
          ·
            refine ⟨402403572651792882993473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268269048434528588662315 402403572651792882993473)
            ·
              refine ⟨301802679488844662245105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402403572651792882993473 301802679488844662245105)
              ·
                refine ⟨226352009616633496683829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301802679488844662245105 226352009616633496683829)
                ·
                  refine ⟨21220500901559390314109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 226352009616633496683829 21220500901559390314109)
                  ·
                    rfl

theorem cell23_371941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_371941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371941 prefixEnd_371941 := by exact prefixLift 371941
  have htrace : WordTrace (prefixWord ++ tailWord_371941) baseStart_371941 baseEnd_371941 := by
    simpa [prefixWord, tailWord_371941, baseEnd_371941] using wordTrace_append hprefix tailTrace_371941
  have hstable : (prefixWord ++ tailWord_371941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371941).length < 2 ^ (prefixWord ++ tailWord_371941).sum := by decide
  have hdescent : baseEnd_371941 < baseStart_371941 := by decide
  rcases family_descends (prefixWord ++ tailWord_371941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371953 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_371953 : Nat := 118140960795 + 371953 * 2 ^ 59
def prefixEnd_371953 : Nat := 4983230072969 + 3 ^ 40 * 371953 * 2
def baseEnd_371953 : Nat := 190990669881888465876925

theorem tailTrace_371953 : CollatzResearch.WordTrace tailWord_371953 prefixEnd_371953 190990669881888465876925 := by
  unfold tailWord_371953
  simp only [CollatzResearch.WordTrace]
  refine ⟨13566240421485280360064513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9044160280990186906709675 13566240421485280360064513)
  ·
    refine ⟨10174680316113960270048385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13566240421485280360064513 10174680316113960270048385)
    ·
      refine ⟨7631010237085470202536289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10174680316113960270048385 7631010237085470202536289)
      ·
        refine ⟨5723257677814102651902217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7631010237085470202536289 5723257677814102651902217)
        ·
          refine ⟨4292443258360576988926663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5723257677814102651902217 4292443258360576988926663)
          ·
            refine ⟨6438664887540865483389995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292443258360576988926663 6438664887540865483389995)
            ·
              refine ⟨9657997331311298225084993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438664887540865483389995 9657997331311298225084993)
              ·
                refine ⟨7243497998483473668813745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9657997331311298225084993 7243497998483473668813745)
                ·
                  refine ⟨5432623498862605251610309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7243497998483473668813745 5432623498862605251610309)
                  ·
                    refine ⟨1018616906036738484676933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5432623498862605251610309 1018616906036738484676933)
                    ·
                      refine ⟨190990669881888465876925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1018616906036738484676933 190990669881888465876925)
                      ·
                        rfl

theorem cell23_371953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_371953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371953 prefixEnd_371953 := by exact prefixLift 371953
  have htrace : WordTrace (prefixWord ++ tailWord_371953) baseStart_371953 baseEnd_371953 := by
    simpa [prefixWord, tailWord_371953, baseEnd_371953] using wordTrace_append hprefix tailTrace_371953
  have hstable : (prefixWord ++ tailWord_371953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371953).length < 2 ^ (prefixWord ++ tailWord_371953).sum := by decide
  have hdescent : baseEnd_371953 < baseStart_371953 := by decide
  rcases family_descends (prefixWord ++ tailWord_371953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_371997 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 6]
def baseStart_371997 : Nat := 118140960795 + 371997 * 2 ^ 59
def prefixEnd_371997 : Nat := 4983230072969 + 3 ^ 40 * 371997 * 2
def baseEnd_371997 : Nat := 21223695892298477080747

theorem tailTrace_371997 : CollatzResearch.WordTrace tailWord_371997 prefixEnd_371997 21223695892298477080747 := by
  unfold tailWord_371997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567845233325875874666245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9045230155550583916444163 13567845233325875874666245)
  ·
    refine ⟨2543970981248601726499921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13567845233325875874666245 2543970981248601726499921)
    ·
      refine ⟨1907978235936451294874941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2543970981248601726499921 1907978235936451294874941)
      ·
        refine ⟨715491838476169235578103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1907978235936451294874941 715491838476169235578103)
        ·
          refine ⟨1073237757714253853367155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715491838476169235578103 1073237757714253853367155)
          ·
            refine ⟨1609856636571380780050733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073237757714253853367155 1609856636571380780050733)
            ·
              refine ⟨603696238714267792519025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1609856636571380780050733 603696238714267792519025)
              ·
                refine ⟨452772179035700844389269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603696238714267792519025 452772179035700844389269)
                ·
                  refine ⟨21223695892298477080747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 452772179035700844389269 21223695892298477080747)
                  ·
                    rfl

theorem cell23_371997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_371997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_371997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_371997 prefixEnd_371997 := by exact prefixLift 371997
  have htrace : WordTrace (prefixWord ++ tailWord_371997) baseStart_371997 baseEnd_371997 := by
    simpa [prefixWord, tailWord_371997, baseEnd_371997] using wordTrace_append hprefix tailTrace_371997
  have hstable : (prefixWord ++ tailWord_371997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_371997).length < 2 ^ (prefixWord ++ tailWord_371997).sum := by decide
  have hdescent : baseEnd_371997 < baseStart_371997 := by decide
  rcases family_descends (prefixWord ++ tailWord_371997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372017 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 1, 5, 2]
def baseStart_372017 : Nat := 118140960795 + 372017 * 2 ^ 59
def prefixEnd_372017 : Nat := 4983230072969 + 3 ^ 40 * 372017 * 2
def baseEnd_372017 : Nat := 191023532643776215476631

theorem tailTrace_372017 : CollatzResearch.WordTrace tailWord_372017 prefixEnd_372017 191023532643776215476631 := by
  unfold tailWord_372017
  simp only [CollatzResearch.WordTrace]
  refine ⟨13568574693253419290394305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9045716462168946193596203 13568574693253419290394305)
  ·
    refine ⟨10176431019940064467795729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13568574693253419290394305 10176431019940064467795729)
    ·
      refine ⟨7632323264955048350846797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10176431019940064467795729 7632323264955048350846797)
      ·
        refine ⟨2862121224358143131567549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7632323264955048350846797 2862121224358143131567549)
        ·
          refine ⟨1073295459134303674337831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2862121224358143131567549 1073295459134303674337831)
          ·
            refine ⟨1609943188701455511506747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073295459134303674337831 1609943188701455511506747)
            ·
              refine ⟨2414914783052183267260121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609943188701455511506747 2414914783052183267260121)
              ·
                refine ⟨1811186087289137450445091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414914783052183267260121 1811186087289137450445091)
                ·
                  refine ⟨2716779130933706175667637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811186087289137450445091 2716779130933706175667637)
                  ·
                    refine ⟨254698043525034953968841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2716779130933706175667637 254698043525034953968841)
                    ·
                      refine ⟨191023532643776215476631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 254698043525034953968841 191023532643776215476631)
                      ·
                        rfl

theorem cell23_372017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_372017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372017 prefixEnd_372017 := by exact prefixLift 372017
  have htrace : WordTrace (prefixWord ++ tailWord_372017) baseStart_372017 baseEnd_372017 := by
    simpa [prefixWord, tailWord_372017, baseEnd_372017] using wordTrace_append hprefix tailTrace_372017
  have hstable : (prefixWord ++ tailWord_372017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372017).length < 2 ^ (prefixWord ++ tailWord_372017).sum := by decide
  have hdescent : baseEnd_372017 < baseStart_372017 := by decide
  rcases family_descends (prefixWord ++ tailWord_372017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_372078 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_372078 : Nat := 118140960795 + 372078 * 2 ^ 59
def prefixEnd_372078 : Nat := 4983230072969 + 3 ^ 40 * 372078 * 2
def baseEnd_372078 : Nat := 63684951654566825604617

theorem tailTrace_372078 : CollatzResearch.WordTrace tailWord_372078 prefixEnd_372078 63684951654566825604617 := by
  unfold tailWord_372078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696349943254053338545611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9047199697354951138909925 1696349943254053338545611)
  ·
    refine ⟨2544524914881080007818417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1696349943254053338545611 2544524914881080007818417)
    ·
      refine ⟨1908393686160810005863813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2544524914881080007818417 1908393686160810005863813)
      ·
        refine ⟨357823816155151876099465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1908393686160810005863813 357823816155151876099465)
        ·
          refine ⟨268367862116363907074599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357823816155151876099465 268367862116363907074599)
          ·
            refine ⟨402551793174545860611899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268367862116363907074599 402551793174545860611899)
            ·
              refine ⟨603827689761818790917849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402551793174545860611899 603827689761818790917849)
              ·
                refine ⟨452870767321364093188387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603827689761818790917849 452870767321364093188387)
                ·
                  refine ⟨679306150982046139782581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452870767321364093188387 679306150982046139782581)
                  ·
                    refine ⟨63684951654566825604617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 679306150982046139782581 63684951654566825604617)
                    ·
                      rfl

theorem cell23_372078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_372078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_372078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_372078 prefixEnd_372078 := by exact prefixLift 372078
  have htrace : WordTrace (prefixWord ++ tailWord_372078) baseStart_372078 baseEnd_372078 := by
    simpa [prefixWord, tailWord_372078, baseEnd_372078] using wordTrace_append hprefix tailTrace_372078
  have hstable : (prefixWord ++ tailWord_372078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_372078).length < 2 ^ (prefixWord ++ tailWord_372078).sum := by decide
  have hdescent : baseEnd_372078 < baseStart_372078 := by decide
  rcases family_descends (prefixWord ++ tailWord_372078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
