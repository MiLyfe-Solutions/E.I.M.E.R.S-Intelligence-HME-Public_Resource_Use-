import V185TrunkScan23Chunk0968

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5736153 : List Nat := [1, 2, 1, 2, 3, 4, 3, 2, 1, 1, 3]
def baseStart_5736153 : Nat := 118140960795 + 5736153 * 2 ^ 59
def prefixEnd_5736153 : Nat := 4983230072969 + 3 ^ 40 * 5736153 * 2
def baseEnd_5736153 : Nat := 2945403596729801008707419

theorem tailTrace_5736153 : CollatzResearch.WordTrace tailWord_5736153 prefixEnd_5736153 2945403596729801008707419 := by
  unfold tailWord_5736153
  simp only [CollatzResearch.WordTrace]
  refine ⟨209214687587904812783037113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139476458391936541855358075 209214687587904812783037113)
  ·
    refine ⟨156911015690928609587277835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209214687587904812783037113 156911015690928609587277835)
    ·
      refine ⟨235366523536392914380916753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156911015690928609587277835 235366523536392914380916753)
      ·
        refine ⟨176524892652294685785687565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235366523536392914380916753 176524892652294685785687565)
        ·
          refine ⟨66196834744610507169632837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176524892652294685785687565 66196834744610507169632837)
          ·
            refine ⟨12411906514614470094306157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66196834744610507169632837 12411906514614470094306157)
            ·
              refine ⟨4654464942980426285364809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12411906514614470094306157 4654464942980426285364809)
              ·
                refine ⟨3490848707235319714023607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4654464942980426285364809 3490848707235319714023607)
                ·
                  refine ⟨5236273060852979571035411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490848707235319714023607 5236273060852979571035411)
                  ·
                    refine ⟨7854409591279469356553117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5236273060852979571035411 7854409591279469356553117)
                    ·
                      refine ⟨2945403596729801008707419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854409591279469356553117 2945403596729801008707419)
                      ·
                        rfl

theorem cell23_5736153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_5736153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736153 prefixEnd_5736153 := by exact prefixLift 5736153
  have htrace : WordTrace (prefixWord ++ tailWord_5736153) baseStart_5736153 baseEnd_5736153 := by
    simpa [prefixWord, tailWord_5736153, baseEnd_5736153] using wordTrace_append hprefix tailTrace_5736153
  have hstable : (prefixWord ++ tailWord_5736153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736153).length < 2 ^ (prefixWord ++ tailWord_5736153).sum := by decide
  have hdescent : baseEnd_5736153 < baseStart_5736153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736179 : List Nat := [1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 3]
def baseStart_5736179 : Nat := 118140960795 + 5736179 * 2 ^ 59
def prefixEnd_5736179 : Nat := 4983230072969 + 3 ^ 40 * 5736179 * 2
def baseEnd_5736179 : Nat := 2945416947226817906982299

theorem tailTrace_5736179 : CollatzResearch.WordTrace tailWord_5736179 prefixEnd_5736179 2945416947226817906982299 := by
  unfold tailWord_5736179
  simp only [CollatzResearch.WordTrace]
  refine ⟨209215635885810619223483591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139477090590540412815655727 209215635885810619223483591)
  ·
    refine ⟨313823453828715928835225387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209215635885810619223483591 313823453828715928835225387)
    ·
      refine ⟨470735180743073893252838081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313823453828715928835225387 470735180743073893252838081)
      ·
        refine ⟨353051385557305419939628561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470735180743073893252838081 353051385557305419939628561)
        ·
          refine ⟨264788539167979064954721421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353051385557305419939628561 264788539167979064954721421)
          ·
            refine ⟨99295702187992149358020533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264788539167979064954721421 99295702187992149358020533)
            ·
              refine ⟨9308972080124264002314425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99295702187992149358020533 9308972080124264002314425)
              ·
                refine ⟨6981729060093198001735819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9308972080124264002314425 6981729060093198001735819)
                ·
                  refine ⟨10472593590139797002603729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981729060093198001735819 10472593590139797002603729)
                  ·
                    refine ⟨7854445192604847751952797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10472593590139797002603729 7854445192604847751952797)
                    ·
                      refine ⟨2945416947226817906982299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854445192604847751952797 2945416947226817906982299)
                      ·
                        rfl

theorem cell23_5736179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_5736179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736179 prefixEnd_5736179 := by exact prefixLift 5736179
  have htrace : WordTrace (prefixWord ++ tailWord_5736179) baseStart_5736179 baseEnd_5736179 := by
    simpa [prefixWord, tailWord_5736179, baseEnd_5736179] using wordTrace_append hprefix tailTrace_5736179
  have hstable : (prefixWord ++ tailWord_5736179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736179).length < 2 ^ (prefixWord ++ tailWord_5736179).sum := by decide
  have hdescent : baseEnd_5736179 < baseStart_5736179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736180 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5736180 : Nat := 118140960795 + 5736180 * 2 ^ 59
def prefixEnd_5736180 : Nat := 4983230072969 + 3 ^ 40 * 5736180 * 2
def baseEnd_5736180 : Nat := 2945417460707472403069795

theorem tailTrace_5736180 : CollatzResearch.WordTrace tailWord_5736180 prefixEnd_5736180 2945417460707472403069795 := by
  unfold tailWord_5736180
  simp only [CollatzResearch.WordTrace]
  refine ⟨104607836179403498197134997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139477114905871330929513329 104607836179403498197134997)
  ·
    refine ⟨4903492320909538977990703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104607836179403498197134997 4903492320909538977990703)
    ·
      refine ⟨7355238481364308466986055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4903492320909538977990703 7355238481364308466986055)
      ·
        refine ⟨11032857722046462700479083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7355238481364308466986055 11032857722046462700479083)
        ·
          refine ⟨16549286583069694050718625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11032857722046462700479083 16549286583069694050718625)
          ·
            refine ⟨12411964937302270538038969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16549286583069694050718625 12411964937302270538038969)
            ·
              refine ⟨9308973702976702903529227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12411964937302270538038969 9308973702976702903529227)
              ·
                refine ⟨13963460554465054355293841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9308973702976702903529227 13963460554465054355293841)
                ·
                  refine ⟨10472595415848790766470381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13963460554465054355293841 10472595415848790766470381)
                  ·
                    refine ⟨3927223280943296537426393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10472595415848790766470381 3927223280943296537426393)
                    ·
                      refine ⟨2945417460707472403069795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927223280943296537426393 2945417460707472403069795)
                      ·
                        rfl

theorem cell23_5736180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5736180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736180 prefixEnd_5736180 := by exact prefixLift 5736180
  have htrace : WordTrace (prefixWord ++ tailWord_5736180) baseStart_5736180 baseEnd_5736180 := by
    simpa [prefixWord, tailWord_5736180, baseEnd_5736180] using wordTrace_append hprefix tailTrace_5736180
  have hstable : (prefixWord ++ tailWord_5736180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736180).length < 2 ^ (prefixWord ++ tailWord_5736180).sum := by decide
  have hdescent : baseEnd_5736180 < baseStart_5736180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736182 : List Nat := [5, 1, 1, 1, 1, 3, 2, 9]
def baseStart_5736182 : Nat := 118140960795 + 5736182 * 2 ^ 59
def prefixEnd_5736182 : Nat := 4983230072969 + 3 ^ 40 * 5736182 * 2
def baseEnd_5736182 : Nat := 109089573617362273897955

theorem tailTrace_5736182 : CollatzResearch.WordTrace tailWord_5736182 prefixEnd_5736182 109089573617362273897955 := by
  unfold tailWord_5736182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075984081549984420990175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139477163536533167157228533 13075984081549984420990175)
  ·
    refine ⟨19613976122324976631485263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13075984081549984420990175 19613976122324976631485263)
    ·
      refine ⟨29420964183487464947227895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19613976122324976631485263 29420964183487464947227895)
      ·
        refine ⟨44131446275231197420841843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29420964183487464947227895 44131446275231197420841843)
        ·
          refine ⟨66197169412846796131262765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44131446275231197420841843 66197169412846796131262765)
          ·
            refine ⟨24823938529817548549223537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66197169412846796131262765 24823938529817548549223537)
            ·
              refine ⟨18617953897363161411917653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24823938529817548549223537 18617953897363161411917653)
              ·
                refine ⟨109089573617362273897955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18617953897363161411917653 109089573617362273897955)
                ·
                  rfl

theorem cell23_5736182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_5736182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736182 prefixEnd_5736182 := by exact prefixLift 5736182
  have htrace : WordTrace (prefixWord ++ tailWord_5736182) baseStart_5736182 baseEnd_5736182 := by
    simpa [prefixWord, tailWord_5736182, baseEnd_5736182] using wordTrace_append hprefix tailTrace_5736182
  have hstable : (prefixWord ++ tailWord_5736182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736182).length < 2 ^ (prefixWord ++ tailWord_5736182).sum := by decide
  have hdescent : baseEnd_5736182 < baseStart_5736182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736192 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3]
def baseStart_5736192 : Nat := 118140960795 + 5736192 * 2 ^ 59
def prefixEnd_5736192 : Nat := 4983230072969 + 3 ^ 40 * 5736192 * 2
def baseEnd_5736192 : Nat := 2945423622475326356119739

theorem tailTrace_5736192 : CollatzResearch.WordTrace tailWord_5736192 prefixEnd_5736192 2945423622475326356119739 := by
  unfold tailWord_5736192
  simp only [CollatzResearch.WordTrace]
  refine ⟨104608055017381761221853415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139477406689842348295804553 104608055017381761221853415)
  ·
    refine ⟨156912082526072641832780123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104608055017381761221853415 156912082526072641832780123)
    ·
      refine ⟨235368123789108962749170185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156912082526072641832780123 235368123789108962749170185)
      ·
        refine ⟨176526092841831722061877639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235368123789108962749170185 176526092841831722061877639)
        ·
          refine ⟨264789139262747583092816459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176526092841831722061877639 264789139262747583092816459)
          ·
            refine ⟨397183708894121374639224689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264789139262747583092816459 397183708894121374639224689)
            ·
              refine ⟨297887781670591030979418517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397183708894121374639224689 297887781670591030979418517)
              ·
                refine ⟨13963489765808954577160243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 297887781670591030979418517 13963489765808954577160243)
                ·
                  refine ⟨20945234648713431865740365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13963489765808954577160243 20945234648713431865740365)
                  ·
                    refine ⟨7854462993267536949652637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20945234648713431865740365 7854462993267536949652637)
                    ·
                      refine ⟨2945423622475326356119739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854462993267536949652637 2945423622475326356119739)
                      ·
                        rfl

theorem cell23_5736192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_5736192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736192 prefixEnd_5736192 := by exact prefixLift 5736192
  have htrace : WordTrace (prefixWord ++ tailWord_5736192) baseStart_5736192 baseEnd_5736192 := by
    simpa [prefixWord, tailWord_5736192, baseEnd_5736192] using wordTrace_append hprefix tailTrace_5736192
  have hstable : (prefixWord ++ tailWord_5736192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736192).length < 2 ^ (prefixWord ++ tailWord_5736192).sum := by decide
  have hdescent : baseEnd_5736192 < baseStart_5736192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736198 : List Nat := [6, 2, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5736198 : Nat := 118140960795 + 5736198 * 2 ^ 59
def prefixEnd_5736198 : Nat := 4983230072969 + 3 ^ 40 * 5736198 * 2
def baseEnd_5736198 : Nat := 981808901119751110881571

theorem tailTrace_5736198 : CollatzResearch.WordTrace tailWord_5736198 prefixEnd_5736198 981808901119751110881571 := by
  unfold tailWord_5736198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538010277273180795888289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139477552581827856978950165 6538010277273180795888289)
  ·
    refine ⟨4903507707954885596916217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6538010277273180795888289 4903507707954885596916217)
    ·
      refine ⟨3677630780966164197687163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4903507707954885596916217 3677630780966164197687163)
      ·
        refine ⟨5516446171449246296530745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677630780966164197687163 5516446171449246296530745)
        ·
          refine ⟨4137334628586934722398059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5516446171449246296530745 4137334628586934722398059)
          ·
            refine ⟨6206001942880402083597089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137334628586934722398059 6206001942880402083597089)
            ·
              refine ⟨4654501457160301562697817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6206001942880402083597089 4654501457160301562697817)
              ·
                refine ⟨3490876092870226172023363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4654501457160301562697817 3490876092870226172023363)
                ·
                  refine ⟨5236314139305339258035045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490876092870226172023363 5236314139305339258035045)
                  ·
                    refine ⟨981808901119751110881571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5236314139305339258035045 981808901119751110881571)
                    ·
                      rfl

theorem cell23_5736198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5736198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736198 prefixEnd_5736198 := by exact prefixLift 5736198
  have htrace : WordTrace (prefixWord ++ tailWord_5736198) baseStart_5736198 baseEnd_5736198 := by
    simpa [prefixWord, tailWord_5736198, baseEnd_5736198] using wordTrace_append hprefix tailTrace_5736198
  have hstable : (prefixWord ++ tailWord_5736198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736198).length < 2 ^ (prefixWord ++ tailWord_5736198).sum := by decide
  have hdescent : baseEnd_5736198 < baseStart_5736198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736226 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_5736226 : Nat := 118140960795 + 5736226 * 2 ^ 59
def prefixEnd_5736226 : Nat := 4983230072969 + 3 ^ 40 * 5736226 * 2
def baseEnd_5736226 : Nat := 2945441080817579223094583

theorem tailTrace_5736226 : CollatzResearch.WordTrace tailWord_5736226 prefixEnd_5736226 2945441080817579223094583 := by
  unfold tailWord_5736226
  simp only [CollatzResearch.WordTrace]
  refine ⟨52304337529160086562611133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139478233411093564166963021 52304337529160086562611133)
  ·
    refine ⟨19614126573435032460979175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52304337529160086562611133 19614126573435032460979175)
    ·
      refine ⟨29421189860152548691468763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19614126573435032460979175 29421189860152548691468763)
      ·
        refine ⟨44131784790228823037203145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29421189860152548691468763 44131784790228823037203145)
        ·
          refine ⟨33098838592671617277902359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44131784790228823037203145 33098838592671617277902359)
          ·
            refine ⟨49648257889007425916853539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33098838592671617277902359 49648257889007425916853539)
            ·
              refine ⟨74472386833511138875280309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49648257889007425916853539 74472386833511138875280309)
              ·
                refine ⟨6981786265641669269557529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74472386833511138875280309 6981786265641669269557529)
                ·
                  refine ⟨5236339699231251952168147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981786265641669269557529 5236339699231251952168147)
                  ·
                    refine ⟨7854509548846877928252221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5236339699231251952168147 7854509548846877928252221)
                    ·
                      refine ⟨2945441080817579223094583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854509548846877928252221 2945441080817579223094583)
                      ·
                        rfl

theorem cell23_5736226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_5736226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736226 prefixEnd_5736226 := by exact prefixLift 5736226
  have htrace : WordTrace (prefixWord ++ tailWord_5736226) baseStart_5736226 baseEnd_5736226 := by
    simpa [prefixWord, tailWord_5736226, baseEnd_5736226] using wordTrace_append hprefix tailTrace_5736226
  have hstable : (prefixWord ++ tailWord_5736226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736226).length < 2 ^ (prefixWord ++ tailWord_5736226).sum := by decide
  have hdescent : baseEnd_5736226 < baseStart_5736226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736252 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_5736252 : Nat := 118140960795 + 5736252 * 2 ^ 59
def prefixEnd_5736252 : Nat := 4983230072969 + 3 ^ 40 * 5736252 * 2
def baseEnd_5736252 : Nat := 2945454431314596121369463

theorem tailTrace_5736252 : CollatzResearch.WordTrace tailWord_5736252 prefixEnd_5736252 2945454431314596121369463 := by
  unfold tailWord_5736252
  simp only [CollatzResearch.WordTrace]
  refine ⟨104609149207273076345445505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139478865609697435127260673 104609149207273076345445505)
  ·
    refine ⟨78456861905454807259084129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104609149207273076345445505 78456861905454807259084129)
    ·
      refine ⟨58842646429091105444313097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78456861905454807259084129 58842646429091105444313097)
      ·
        refine ⟨44131984821818329083234823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58842646429091105444313097 44131984821818329083234823)
        ·
          refine ⟨66197977232727493624852235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44131984821818329083234823 66197977232727493624852235)
          ·
            refine ⟨99296965849091240437278353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66197977232727493624852235 99296965849091240437278353)
            ·
              refine ⟨74472724386818430327958765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99296965849091240437278353 74472724386818430327958765)
              ·
                refine ⟨27927271645056911372984537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74472724386818430327958765 27927271645056911372984537)
                ·
                  refine ⟨20945453733792683529738403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27927271645056911372984537 20945453733792683529738403)
                  ·
                    refine ⟨31418180600689025294607605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20945453733792683529738403 31418180600689025294607605)
                    ·
                      refine ⟨2945454431314596121369463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31418180600689025294607605 2945454431314596121369463)
                      ·
                        rfl

theorem cell23_5736252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_5736252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736252 prefixEnd_5736252 := by exact prefixLift 5736252
  have htrace : WordTrace (prefixWord ++ tailWord_5736252) baseStart_5736252 baseEnd_5736252 := by
    simpa [prefixWord, tailWord_5736252, baseEnd_5736252] using wordTrace_append hprefix tailTrace_5736252
  have hstable : (prefixWord ++ tailWord_5736252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736252).length < 2 ^ (prefixWord ++ tailWord_5736252).sum := by decide
  have hdescent : baseEnd_5736252 < baseStart_5736252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736253 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5736253 : Nat := 118140960795 + 5736253 * 2 ^ 59
def prefixEnd_5736253 : Nat := 4983230072969 + 3 ^ 40 * 5736253 * 2
def baseEnd_5736253 : Nat := 2945454944795250617456959

theorem tailTrace_5736253 : CollatzResearch.WordTrace tailWord_5736253 prefixEnd_5736253 2945454944795250617456959 := by
  unfold tailWord_5736253
  simp only [CollatzResearch.WordTrace]
  refine ⟨209218334887542529861677413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139478889925028353241118275 209218334887542529861677413)
  ·
    refine ⟨39228437791414224349064515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209218334887542529861677413 39228437791414224349064515)
    ·
      refine ⟨58842656687121336523596773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39228437791414224349064515 58842656687121336523596773)
      ·
        refine ⟨11032998128835250598174395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58842656687121336523596773 11032998128835250598174395)
        ·
          refine ⟨16549497193252875897261593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11032998128835250598174395 16549497193252875897261593)
          ·
            refine ⟨12412122894939656922946195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16549497193252875897261593 12412122894939656922946195)
            ·
              refine ⟨18618184342409485384419293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12412122894939656922946195 18618184342409485384419293)
              ·
                refine ⟨6981819128403557019157235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18618184342409485384419293 6981819128403557019157235)
                ·
                  refine ⟨10472728692605335528735853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981819128403557019157235 10472728692605335528735853)
                  ·
                    refine ⟨3927273259727000823275945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10472728692605335528735853 3927273259727000823275945)
                    ·
                      refine ⟨2945454944795250617456959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927273259727000823275945 2945454944795250617456959)
                      ·
                        rfl

theorem cell23_5736253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5736253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736253 prefixEnd_5736253 := by exact prefixLift 5736253
  have htrace : WordTrace (prefixWord ++ tailWord_5736253) baseStart_5736253 baseEnd_5736253 := by
    simpa [prefixWord, tailWord_5736253, baseEnd_5736253] using wordTrace_append hprefix tailTrace_5736253
  have hstable : (prefixWord ++ tailWord_5736253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736253).length < 2 ^ (prefixWord ++ tailWord_5736253).sum := by decide
  have hdescent : baseEnd_5736253 < baseStart_5736253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736266 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_5736266 : Nat := 118140960795 + 5736266 * 2 ^ 59
def prefixEnd_5736266 : Nat := 4983230072969 + 3 ^ 40 * 5736266 * 2
def baseEnd_5736266 : Nat := 2945461620043759066594399

theorem tailTrace_5736266 : CollatzResearch.WordTrace tailWord_5736266 prefixEnd_5736266 2945461620043759066594399 := by
  unfold tailWord_5736266
  simp only [CollatzResearch.WordTrace]
  refine ⟨52304702259123858270475163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139479206024330288721267101 52304702259123858270475163)
  ·
    refine ⟨78457053388685787405712745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52304702259123858270475163 78457053388685787405712745)
    ·
      refine ⟨58842790041514340554284559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78457053388685787405712745 58842790041514340554284559)
      ·
        refine ⟨88264185062271510831426839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58842790041514340554284559 88264185062271510831426839)
        ·
          refine ⟨132396277593407266247140259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88264185062271510831426839 132396277593407266247140259)
          ·
            refine ⟨198594416390110899370710389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132396277593407266247140259 198594416390110899370710389)
            ·
              refine ⟨18618226536572896816004099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198594416390110899370710389 18618226536572896816004099)
              ·
                refine ⟨27927339804859345224006149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18618226536572896816004099 27927339804859345224006149)
                ·
                  refine ⟨5236376213411127229501153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27927339804859345224006149 5236376213411127229501153)
                  ·
                    refine ⟨3927282160058345422125865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5236376213411127229501153 3927282160058345422125865)
                    ·
                      refine ⟨2945461620043759066594399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927282160058345422125865 2945461620043759066594399)
                      ·
                        rfl

theorem cell23_5736266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_5736266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736266 prefixEnd_5736266 := by exact prefixLift 5736266
  have htrace : WordTrace (prefixWord ++ tailWord_5736266) baseStart_5736266 baseEnd_5736266 := by
    simpa [prefixWord, tailWord_5736266, baseEnd_5736266] using wordTrace_append hprefix tailTrace_5736266
  have hstable : (prefixWord ++ tailWord_5736266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736266).length < 2 ^ (prefixWord ++ tailWord_5736266).sum := by decide
  have hdescent : baseEnd_5736266 < baseStart_5736266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736334 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5736334 : Nat := 118140960795 + 5736334 * 2 ^ 59
def prefixEnd_5736334 : Nat := 4983230072969 + 3 ^ 40 * 5736334 * 2
def baseEnd_5736334 : Nat := 2945496536728264800544087

theorem tailTrace_5736334 : CollatzResearch.WordTrace tailWord_5736334 prefixEnd_5736334 2945496536728264800544087 := by
  unfold tailWord_5736334
  simp only [CollatzResearch.WordTrace]
  refine ⟨26152661150031135086922007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139480859466832720463584037 26152661150031135086922007)
  ·
    refine ⟨39228991725046702630383011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26152661150031135086922007 39228991725046702630383011)
    ·
      refine ⟨58843487587570053945574517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39228991725046702630383011 58843487587570053945574517)
      ·
        refine ⟨5516576961334692557397611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58843487587570053945574517 5516576961334692557397611)
        ·
          refine ⟨8274865442002038836096417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516576961334692557397611 8274865442002038836096417)
          ·
            refine ⟨6206149081501529127072313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8274865442002038836096417 6206149081501529127072313)
            ·
              refine ⟨4654611811126146845304235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6206149081501529127072313 4654611811126146845304235)
              ·
                refine ⟨6981917716689220267956353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654611811126146845304235 6981917716689220267956353)
                ·
                  refine ⟨5236438287516915200967265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981917716689220267956353 5236438287516915200967265)
                  ·
                    refine ⟨3927328715637686400725449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5236438287516915200967265 3927328715637686400725449)
                    ·
                      refine ⟨2945496536728264800544087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927328715637686400725449 2945496536728264800544087)
                      ·
                        rfl

theorem cell23_5736334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5736334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736334 prefixEnd_5736334 := by exact prefixLift 5736334
  have htrace : WordTrace (prefixWord ++ tailWord_5736334) baseStart_5736334 baseEnd_5736334 := by
    simpa [prefixWord, tailWord_5736334, baseEnd_5736334] using wordTrace_append hprefix tailTrace_5736334
  have hstable : (prefixWord ++ tailWord_5736334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736334).length < 2 ^ (prefixWord ++ tailWord_5736334).sum := by decide
  have hdescent : baseEnd_5736334 < baseStart_5736334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736339 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 6, 4, 2]
def baseStart_5736339 : Nat := 118140960795 + 5736339 * 2 ^ 59
def prefixEnd_5736339 : Nat := 4983230072969 + 3 ^ 40 * 5736339 * 2
def baseEnd_5736339 : Nat := 2945499104131537280981563

theorem tailTrace_5736339 : CollatzResearch.WordTrace tailWord_5736339 prefixEnd_5736339 2945499104131537280981563 := by
  unfold tailWord_5736339
  simp only [CollatzResearch.WordTrace]
  refine ⟨209221471565230966549308071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139480981043487311032872047 209221471565230966549308071)
  ·
    refine ⟨313832207347846449823962107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209221471565230966549308071 313832207347846449823962107)
    ·
      refine ⟨470748311021769674735943161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313832207347846449823962107 470748311021769674735943161)
      ·
        refine ⟨353061233266327256051957371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470748311021769674735943161 353061233266327256051957371)
        ·
          refine ⟨529591849899490884077936057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353061233266327256051957371 529591849899490884077936057)
          ·
            refine ⟨397193887424618163058452043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529591849899490884077936057 397193887424618163058452043)
            ·
              refine ⟨595790831136927244587678065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397193887424618163058452043 595790831136927244587678065)
              ·
                refine ⟨446843123352695433440758549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 595790831136927244587678065 446843123352695433440758549)
                ·
                  refine ⟨20945771407157598442535557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 446843123352695433440758549 20945771407157598442535557)
                  ·
                    refine ⟨3927332138842049707975417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20945771407157598442535557 3927332138842049707975417)
                    ·
                      refine ⟨2945499104131537280981563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927332138842049707975417 2945499104131537280981563)
                      ·
                        rfl

theorem cell23_5736339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 4, 2].length) (baseStart_5736339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736339 prefixEnd_5736339 := by exact prefixLift 5736339
  have htrace : WordTrace (prefixWord ++ tailWord_5736339) baseStart_5736339 baseEnd_5736339 := by
    simpa [prefixWord, tailWord_5736339, baseEnd_5736339] using wordTrace_append hprefix tailTrace_5736339
  have hstable : (prefixWord ++ tailWord_5736339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736339).length < 2 ^ (prefixWord ++ tailWord_5736339).sum := by decide
  have hdescent : baseEnd_5736339 < baseStart_5736339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736352 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6]
def baseStart_5736352 : Nat := 118140960795 + 5736352 * 2 ^ 59
def prefixEnd_5736352 : Nat := 4983230072969 + 3 ^ 40 * 5736352 * 2
def baseEnd_5736352 : Nat := 2945505779380045730119003

theorem tailTrace_5736352 : CollatzResearch.WordTrace tailWord_5736352 prefixEnd_5736352 2945505779380045730119003 := by
  unfold tailWord_5736352
  simp only [CollatzResearch.WordTrace]
  refine ⟨104610972857091934884765655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139481297142789246513020873 104610972857091934884765655)
  ·
    refine ⟨156916459285637902327148483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104610972857091934884765655 156916459285637902327148483)
    ·
      refine ⟨235374688928456853490722725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156916459285637902327148483 235374688928456853490722725)
      ·
        refine ⟨44132754174085660029510511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235374688928456853490722725 44132754174085660029510511)
        ·
          refine ⟨66199131261128490044265767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44132754174085660029510511 66199131261128490044265767)
          ·
            refine ⟨99298696891692735066398651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66199131261128490044265767 99298696891692735066398651)
            ·
              refine ⟨148948045337539102599597977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99298696891692735066398651 148948045337539102599597977)
              ·
                refine ⟨111711034003154326949698483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148948045337539102599597977 111711034003154326949698483)
                ·
                  refine ⟨167566551004731490424547725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111711034003154326949698483 167566551004731490424547725)
                  ·
                    refine ⟨62837456626774308909205397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167566551004731490424547725 62837456626774308909205397)
                    ·
                      refine ⟨2945505779380045730119003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62837456626774308909205397 2945505779380045730119003)
                      ·
                        rfl

theorem cell23_5736352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_5736352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736352 prefixEnd_5736352 := by exact prefixLift 5736352
  have htrace : WordTrace (prefixWord ++ tailWord_5736352) baseStart_5736352 baseEnd_5736352 := by
    simpa [prefixWord, tailWord_5736352, baseEnd_5736352] using wordTrace_append hprefix tailTrace_5736352
  have hstable : (prefixWord ++ tailWord_5736352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736352).length < 2 ^ (prefixWord ++ tailWord_5736352).sum := by decide
  have hdescent : baseEnd_5736352 < baseStart_5736352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736356 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_5736356 : Nat := 118140960795 + 5736356 * 2 ^ 59
def prefixEnd_5736356 : Nat := 4983230072969 + 3 ^ 40 * 5736356 * 2
def baseEnd_5736356 : Nat := 2945507833302663714468985

theorem tailTrace_5736356 : CollatzResearch.WordTrace tailWord_5736356 prefixEnd_5736356 2945507833302663714468985 := by
  unfold tailWord_5736356
  simp only [CollatzResearch.WordTrace]
  refine ⟨104611045803084689226338461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139481394404112918968451281 104611045803084689226338461)
  ·
    refine ⟨39229142176156758459876923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104611045803084689226338461 39229142176156758459876923)
    ·
      refine ⟨58843713264235137689815385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39229142176156758459876923 58843713264235137689815385)
      ·
        refine ⟨44132784948176353267361539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58843713264235137689815385 44132784948176353267361539)
        ·
          refine ⟨66199177422264529901042309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44132784948176353267361539 66199177422264529901042309)
          ·
            refine ⟨12412345766674599356445433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66199177422264529901042309 12412345766674599356445433)
            ·
              refine ⟨9309259325005949517334075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12412345766674599356445433 9309259325005949517334075)
              ·
                refine ⟨13963888987508924276001113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9309259325005949517334075 13963888987508924276001113)
                ·
                  refine ⟨10472916740631693207000835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13963888987508924276001113 10472916740631693207000835)
                  ·
                    refine ⟨15709375110947539810501253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10472916740631693207000835 15709375110947539810501253)
                    ·
                      refine ⟨2945507833302663714468985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15709375110947539810501253 2945507833302663714468985)
                      ·
                        rfl

theorem cell23_5736356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_5736356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736356 prefixEnd_5736356 := by exact prefixLift 5736356
  have htrace : WordTrace (prefixWord ++ tailWord_5736356) baseStart_5736356 baseEnd_5736356 := by
    simpa [prefixWord, tailWord_5736356, baseEnd_5736356] using wordTrace_append hprefix tailTrace_5736356
  have hstable : (prefixWord ++ tailWord_5736356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736356).length < 2 ^ (prefixWord ++ tailWord_5736356).sum := by decide
  have hdescent : baseEnd_5736356 < baseStart_5736356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736410 : List Nat := [3, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3]
def baseStart_5736410 : Nat := 118140960795 + 5736410 * 2 ^ 59
def prefixEnd_5736410 : Nat := 4983230072969 + 3 ^ 40 * 5736410 * 2
def baseEnd_5736410 : Nat := 2945535561258006503193737

theorem tailTrace_5736410 : CollatzResearch.WordTrace tailWord_5736410 prefixEnd_5736410 2945535561258006503193737 := by
  unfold tailWord_5736410
  simp only [CollatzResearch.WordTrace]
  refine ⟨52306015286993436418785671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139482707431982497116761789 52306015286993436418785671)
  ·
    refine ⟨78459022930490154628178507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52306015286993436418785671 78459022930490154628178507)
    ·
      refine ⟨117688534395735231942267761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78459022930490154628178507 117688534395735231942267761)
      ·
        refine ⟨88266400796801423956700821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117688534395735231942267761 88266400796801423956700821)
        ·
          refine ⟨4137487537350066747970351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88266400796801423956700821 4137487537350066747970351)
          ·
            refine ⟨6206231306025100121955527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137487537350066747970351 6206231306025100121955527)
            ·
              refine ⟨9309346959037650182933291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206231306025100121955527 9309346959037650182933291)
              ·
                refine ⟨13964020438556475274399937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9309346959037650182933291 13964020438556475274399937)
                ·
                  refine ⟨10473015328917356455799953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13964020438556475274399937 10473015328917356455799953)
                  ·
                    refine ⟨7854761496688017341849965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10473015328917356455799953 7854761496688017341849965)
                    ·
                      refine ⟨2945535561258006503193737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854761496688017341849965 2945535561258006503193737)
                      ·
                        rfl

theorem cell23_5736410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_5736410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736410 prefixEnd_5736410 := by exact prefixLift 5736410
  have htrace : WordTrace (prefixWord ++ tailWord_5736410) baseStart_5736410 baseEnd_5736410 := by
    simpa [prefixWord, tailWord_5736410, baseEnd_5736410] using wordTrace_append hprefix tailTrace_5736410
  have hstable : (prefixWord ++ tailWord_5736410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736410).length < 2 ^ (prefixWord ++ tailWord_5736410).sum := by decide
  have hdescent : baseEnd_5736410 < baseStart_5736410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736426 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_5736426 : Nat := 118140960795 + 5736426 * 2 ^ 59
def prefixEnd_5736426 : Nat := 4983230072969 + 3 ^ 40 * 5736426 * 2
def baseEnd_5736426 : Nat := 981847925649492813531221

theorem tailTrace_5736426 : CollatzResearch.WordTrace tailWord_5736426 prefixEnd_5736426 981847925649492813531221 := by
  unfold tailWord_5736426
  simp only [CollatzResearch.WordTrace]
  refine ⟨52306161178978945101931283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139483096477277186938483421 52306161178978945101931283)
  ·
    refine ⟨78459241768468417652896925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52306161178978945101931283 78459241768468417652896925)
    ·
      refine ⟨29422215663175656619836347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78459241768468417652896925 29422215663175656619836347)
      ·
        refine ⟨44133323494763484929754521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29422215663175656619836347 44133323494763484929754521)
        ·
          refine ⟨33099992621072613697315891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44133323494763484929754521 33099992621072613697315891)
          ·
            refine ⟨49649988931608920545973837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33099992621072613697315891 49649988931608920545973837)
            ·
              refine ⟨18618745849353345204740189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49649988931608920545973837 18618745849353345204740189)
              ·
                refine ⟨6982029693507504451777571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18618745849353345204740189 6982029693507504451777571)
                ·
                  refine ⟨10473044540261256677666357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982029693507504451777571 10473044540261256677666357)
                  ·
                    refine ⟨981847925649492813531221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10473044540261256677666357 981847925649492813531221)
                    ·
                      rfl

theorem cell23_5736426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_5736426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736426 prefixEnd_5736426 := by exact prefixLift 5736426
  have htrace : WordTrace (prefixWord ++ tailWord_5736426) baseStart_5736426 baseEnd_5736426 := by
    simpa [prefixWord, tailWord_5736426, baseEnd_5736426] using wordTrace_append hprefix tailTrace_5736426
  have hstable : (prefixWord ++ tailWord_5736426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736426).length < 2 ^ (prefixWord ++ tailWord_5736426).sum := by decide
  have hdescent : baseEnd_5736426 < baseStart_5736426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736459 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6]
def baseStart_5736459 : Nat := 118140960795 + 5736459 * 2 ^ 59
def prefixEnd_5736459 : Nat := 4983230072969 + 3 ^ 40 * 5736459 * 2
def baseEnd_5736459 : Nat := 2945560721810076811481011

theorem tailTrace_5736459 : CollatzResearch.WordTrace tailWord_5736459 prefixEnd_5736459 2945560721810076811481011 := by
  unfold tailWord_5736459
  simp only [CollatzResearch.WordTrace]
  refine ⟨209225848324796227043676431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139483898883197484695784287 209225848324796227043676431)
  ·
    refine ⟨313838772487194340565514647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209225848324796227043676431 313838772487194340565514647)
    ·
      refine ⟨470758158730791510848271971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313838772487194340565514647 470758158730791510848271971)
      ·
        refine ⟨706137238096187266272407957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470758158730791510848271971 706137238096187266272407957)
        ·
          refine ⟨33100183035758778106519123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 706137238096187266272407957 33100183035758778106519123)
          ·
            refine ⟨49650274553638167159778685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33100183035758778106519123 49650274553638167159778685)
            ·
              refine ⟨18618852957614312684917007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49650274553638167159778685 18618852957614312684917007)
              ·
                refine ⟨27928279436421469027375511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18618852957614312684917007 27928279436421469027375511)
                ·
                  refine ⟨41892419154632203541063267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27928279436421469027375511 41892419154632203541063267)
                  ·
                    refine ⟨62838628731948305311594901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41892419154632203541063267 62838628731948305311594901)
                    ·
                      refine ⟨2945560721810076811481011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62838628731948305311594901 2945560721810076811481011)
                      ·
                        rfl

theorem cell23_5736459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_5736459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736459 prefixEnd_5736459 := by exact prefixLift 5736459
  have htrace : WordTrace (prefixWord ++ tailWord_5736459) baseStart_5736459 baseEnd_5736459 := by
    simpa [prefixWord, tailWord_5736459, baseEnd_5736459] using wordTrace_append hprefix tailTrace_5736459
  have hstable : (prefixWord ++ tailWord_5736459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736459).length < 2 ^ (prefixWord ++ tailWord_5736459).sum := by decide
  have hdescent : baseEnd_5736459 < baseStart_5736459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736506 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2]
def baseStart_5736506 : Nat := 118140960795 + 5736506 * 2 ^ 59
def prefixEnd_5736506 : Nat := 4983230072969 + 3 ^ 40 * 5736506 * 2
def baseEnd_5736506 : Nat := 2945584855400838127593295

theorem tailTrace_5736506 : CollatzResearch.WordTrace tailWord_5736506 prefixEnd_5736506 2945584855400838127593295 := by
  unfold tailWord_5736506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52306890638906488517659343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139485041703750636047091581 52306890638906488517659343)
  ·
    refine ⟨78460335958359732776489015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52306890638906488517659343 78460335958359732776489015)
    ·
      refine ⟨117690503937539599164733523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78460335958359732776489015 117690503937539599164733523)
      ·
        refine ⟨176535755906309398747100285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117690503937539599164733523 176535755906309398747100285)
        ·
          refine ⟨66200908464866024530162607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176535755906309398747100285 66200908464866024530162607)
          ·
            refine ⟨99301362697299036795243911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66200908464866024530162607 99301362697299036795243911)
            ·
              refine ⟨148952044045948555192865867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99301362697299036795243911 148952044045948555192865867)
              ·
                refine ⟨223428066068922832789298801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148952044045948555192865867 223428066068922832789298801)
                ·
                  refine ⟨167571049551692124591974101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223428066068922832789298801 167571049551692124591974101)
                  ·
                    refine ⟨3927446473867784170124393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167571049551692124591974101 3927446473867784170124393)
                    ·
                      refine ⟨2945584855400838127593295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927446473867784170124393 2945584855400838127593295)
                      ·
                        rfl

theorem cell23_5736506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_5736506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736506 prefixEnd_5736506 := by exact prefixLift 5736506
  have htrace : WordTrace (prefixWord ++ tailWord_5736506) baseStart_5736506 baseEnd_5736506 := by
    simpa [prefixWord, tailWord_5736506, baseEnd_5736506] using wordTrace_append hprefix tailTrace_5736506
  have hstable : (prefixWord ++ tailWord_5736506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736506).length < 2 ^ (prefixWord ++ tailWord_5736506).sum := by decide
  have hdescent : baseEnd_5736506 < baseStart_5736506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736529 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 4, 6]
def baseStart_5736529 : Nat := 118140960795 + 5736529 * 2 ^ 59
def prefixEnd_5736529 : Nat := 4983230072969 + 3 ^ 40 * 5736529 * 2
def baseEnd_5736529 : Nat := 981865555151963845868563

theorem tailTrace_5736529 : CollatzResearch.WordTrace tailWord_5736529 prefixEnd_5736529 981865555151963845868563 := by
  unfold tailWord_5736529
  simp only [CollatzResearch.WordTrace]
  refine ⟨209228401434542628998724641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139485600956361752665816427 209228401434542628998724641)
  ·
    refine ⟨156921301075906971749043481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209228401434542628998724641 156921301075906971749043481)
    ·
      refine ⟨117690975806930228811782611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156921301075906971749043481 117690975806930228811782611)
      ·
        refine ⟨176536463710395343217673917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117690975806930228811782611 176536463710395343217673917)
        ·
          refine ⟨66201173891398253706627719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176536463710395343217673917 66201173891398253706627719)
          ·
            refine ⟨99301760837097380559941579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66201173891398253706627719 99301760837097380559941579)
            ·
              refine ⟨148952641255646070839912369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99301760837097380559941579 148952641255646070839912369)
              ·
                refine ⟨111714480941734553129934277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148952641255646070839912369 111714480941734553129934277)
                ·
                  refine ⟨20946465176575228711862677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111714480941734553129934277 20946465176575228711862677)
                  ·
                    refine ⟨981865555151963845868563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20946465176575228711862677 981865555151963845868563)
                    ·
                      rfl

theorem cell23_5736529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_5736529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736529 prefixEnd_5736529 := by exact prefixLift 5736529
  have htrace : WordTrace (prefixWord ++ tailWord_5736529) baseStart_5736529 baseEnd_5736529 := by
    simpa [prefixWord, tailWord_5736529, baseEnd_5736529] using wordTrace_append hprefix tailTrace_5736529
  have hstable : (prefixWord ++ tailWord_5736529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736529).length < 2 ^ (prefixWord ++ tailWord_5736529).sum := by decide
  have hdescent : baseEnd_5736529 < baseStart_5736529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736534 : List Nat := [5, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_5736534 : Nat := 118140960795 + 5736534 * 2 ^ 59
def prefixEnd_5736534 : Nat := 4983230072969 + 3 ^ 40 * 5736534 * 2
def baseEnd_5736534 : Nat := 2945599232859164018043167

theorem tailTrace_5736534 : CollatzResearch.WordTrace tailWord_5736534 prefixEnd_5736534 2945599232859164018043167 := by
  unfold tailWord_5736534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13076786487470282178291041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139485722533016343235104437 13076786487470282178291041)
  ·
    refine ⟨9807589865602711633718281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13076786487470282178291041 9807589865602711633718281)
    ·
      refine ⟨7355692399202033725288711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9807589865602711633718281 7355692399202033725288711)
      ·
        refine ⟨11033538598803050587933067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7355692399202033725288711 11033538598803050587933067)
        ·
          refine ⟨16550307898204575881899601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11033538598803050587933067 16550307898204575881899601)
          ·
            refine ⟨12412730923653431911424701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16550307898204575881899601 12412730923653431911424701)
            ·
              refine ⟨4654774096370036966784263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12412730923653431911424701 4654774096370036966784263)
              ·
                refine ⟨6982161144555055450176395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654774096370036966784263 6982161144555055450176395)
                ·
                  refine ⟨10473241716832583175264593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982161144555055450176395 10473241716832583175264593)
                  ·
                    refine ⟨7854931287624437381448445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10473241716832583175264593 7854931287624437381448445)
                    ·
                      refine ⟨2945599232859164018043167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854931287624437381448445 2945599232859164018043167)
                      ·
                        rfl

theorem cell23_5736534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_5736534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736534 prefixEnd_5736534 := by exact prefixLift 5736534
  have htrace : WordTrace (prefixWord ++ tailWord_5736534) baseStart_5736534 baseEnd_5736534 := by
    simpa [prefixWord, tailWord_5736534, baseEnd_5736534] using wordTrace_append hprefix tailTrace_5736534
  have hstable : (prefixWord ++ tailWord_5736534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736534).length < 2 ^ (prefixWord ++ tailWord_5736534).sum := by decide
  have hdescent : baseEnd_5736534 < baseStart_5736534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736556 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_5736556 : Nat := 118140960795 + 5736556 * 2 ^ 59
def prefixEnd_5736556 : Nat := 4983230072969 + 3 ^ 40 * 5736556 * 2
def baseEnd_5736556 : Nat := 2945610529433562931968065

theorem tailTrace_5736556 : CollatzResearch.WordTrace tailWord_5736556 prefixEnd_5736556 2945610529433562931968065 := by
  unfold tailWord_5736556
  simp only [CollatzResearch.WordTrace]
  refine ⟨104614693102722406304978761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139486257470296541739971681 104614693102722406304978761)
  ·
    refine ⟨78461019827041804728734071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104614693102722406304978761 78461019827041804728734071)
    ·
      refine ⟨117691529740562707093101107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78461019827041804728734071 117691529740562707093101107)
      ·
        refine ⟨176537294610844060639651661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117691529740562707093101107 176537294610844060639651661)
        ·
          refine ⟨66201485479066522739869373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176537294610844060639651661 66201485479066522739869373)
          ·
            refine ⟨24825557054649946027451015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66201485479066522739869373 24825557054649946027451015)
            ·
              refine ⟨37238335581974919041176523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24825557054649946027451015 37238335581974919041176523)
              ·
                refine ⟨55857503372962378561764785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37238335581974919041176523 55857503372962378561764785)
                ·
                  refine ⟨41893127529721783921323589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55857503372962378561764785 41893127529721783921323589)
                  ·
                    refine ⟨7854961411822834485248173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41893127529721783921323589 7854961411822834485248173)
                    ·
                      refine ⟨2945610529433562931968065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854961411822834485248173 2945610529433562931968065)
                      ·
                        rfl

theorem cell23_5736556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_5736556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736556 prefixEnd_5736556 := by exact prefixLift 5736556
  have htrace : WordTrace (prefixWord ++ tailWord_5736556) baseStart_5736556 baseEnd_5736556 := by
    simpa [prefixWord, tailWord_5736556, baseEnd_5736556] using wordTrace_append hprefix tailTrace_5736556
  have hstable : (prefixWord ++ tailWord_5736556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736556).length < 2 ^ (prefixWord ++ tailWord_5736556).sum := by decide
  have hdescent : baseEnd_5736556 < baseStart_5736556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736610 : List Nat := [3, 3, 1, 3, 1, 1, 2, 4, 5]
def baseStart_5736610 : Nat := 118140960795 + 5736610 * 2 ^ 59
def prefixEnd_5736610 : Nat := 4983230072969 + 3 ^ 40 * 5736610 * 2
def baseEnd_5736610 : Nat := 327293139709878413410313

theorem tailTrace_5736610 : CollatzResearch.WordTrace tailWord_5736610 prefixEnd_5736610 327293139709878413410313 := by
  unfold tailWord_5736610
  simp only [CollatzResearch.WordTrace]
  refine ⟨52307838936812294958105821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139487570498166119888282189 52307838936812294958105821)
  ·
    refine ⟨19615439601304610609289683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52307838936812294958105821 19615439601304610609289683)
    ·
      refine ⟨29423159401956915913934525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19615439601304610609289683 29423159401956915913934525)
      ·
        refine ⟨11033684775733843467725447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29423159401956915913934525 11033684775733843467725447)
        ·
          refine ⟨16550527163600765201588171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11033684775733843467725447 16550527163600765201588171)
          ·
            refine ⟨24825790745401147802382257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16550527163600765201588171 24825790745401147802382257)
            ·
              refine ⟨18619343059050860851786693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24825790745401147802382257 18619343059050860851786693)
              ·
                refine ⟨3491126823572036409710005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18619343059050860851786693 3491126823572036409710005)
                ·
                  refine ⟨327293139709878413410313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3491126823572036409710005 327293139709878413410313)
                  ·
                    rfl

theorem cell23_5736610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_5736610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736610 prefixEnd_5736610 := by exact prefixLift 5736610
  have htrace : WordTrace (prefixWord ++ tailWord_5736610) baseStart_5736610 baseEnd_5736610 := by
    simpa [prefixWord, tailWord_5736610, baseEnd_5736610] using wordTrace_append hprefix tailTrace_5736610
  have hstable : (prefixWord ++ tailWord_5736610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736610).length < 2 ^ (prefixWord ++ tailWord_5736610).sum := by decide
  have hdescent : baseEnd_5736610 < baseStart_5736610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736626 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_5736626 : Nat := 118140960795 + 5736626 * 2 ^ 59
def prefixEnd_5736626 : Nat := 4983230072969 + 3 ^ 40 * 5736626 * 2
def baseEnd_5736626 : Nat := 2945646473079377658092743

theorem tailTrace_5736626 : CollatzResearch.WordTrace tailWord_5736626 prefixEnd_5736626 2945646473079377658092743 := by
  unfold tailWord_5736626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52307984828797803641251433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139487959543460809710003821 52307984828797803641251433)
  ·
    refine ⟨39230988621598352730938575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52307984828797803641251433 39230988621598352730938575)
    ·
      refine ⟨58846482932397529096407863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39230988621598352730938575 58846482932397529096407863)
      ·
        refine ⟨88269724398596293644611795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58846482932397529096407863 88269724398596293644611795)
        ·
          refine ⟨132404586597894440466917693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88269724398596293644611795 132404586597894440466917693)
          ·
            refine ⟨49651719974210415175094135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132404586597894440466917693 49651719974210415175094135)
            ·
              refine ⟨74477579961315622762641203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49651719974210415175094135 74477579961315622762641203)
              ·
                refine ⟨111716369941973434143961805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74477579961315622762641203 111716369941973434143961805)
                ·
                  refine ⟨41893638728240037803985677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111716369941973434143961805 41893638728240037803985677)
                  ·
                    refine ⟨15710114523090014176494629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41893638728240037803985677 15710114523090014176494629)
                    ·
                      refine ⟨2945646473079377658092743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15710114523090014176494629 2945646473079377658092743)
                      ·
                        rfl

theorem cell23_5736626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_5736626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736626 prefixEnd_5736626 := by exact prefixLift 5736626
  have htrace : WordTrace (prefixWord ++ tailWord_5736626) baseStart_5736626 baseEnd_5736626 := by
    simpa [prefixWord, tailWord_5736626, baseEnd_5736626] using wordTrace_append hprefix tailTrace_5736626
  have hstable : (prefixWord ++ tailWord_5736626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736626).length < 2 ^ (prefixWord ++ tailWord_5736626).sum := by decide
  have hdescent : baseEnd_5736626 < baseStart_5736626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736666 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 8]
def baseStart_5736666 : Nat := 118140960795 + 5736666 * 2 ^ 59
def prefixEnd_5736666 : Nat := 4983230072969 + 3 ^ 40 * 5736666 * 2
def baseEnd_5736666 : Nat := 327296334700617500176951

theorem tailTrace_5736666 : CollatzResearch.WordTrace tailWord_5736666 prefixEnd_5736666 327296334700617500176951 := by
  unfold tailWord_5736666
  simp only [CollatzResearch.WordTrace]
  refine ⟨52308349558761575349115463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139488932156697534264307901 52308349558761575349115463)
  ·
    refine ⟨78462524338142363023673195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52308349558761575349115463 78462524338142363023673195)
    ·
      refine ⟨117693786507213544535509793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78462524338142363023673195 117693786507213544535509793)
      ·
        refine ⟨88270339880410158401632345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117693786507213544535509793 88270339880410158401632345)
        ·
          refine ⟨66202754910307618801224259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88270339880410158401632345 66202754910307618801224259)
          ·
            refine ⟨99304132365461428201836389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66202754910307618801224259 99304132365461428201836389)
            ·
              refine ⟨18619524818524017787844323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99304132365461428201836389 18619524818524017787844323)
              ·
                refine ⟨27929287227786026681766485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18619524818524017787844323 27929287227786026681766485)
                ·
                  refine ⟨327296334700617500176951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27929287227786026681766485 327296334700617500176951)
                  ·
                    rfl

theorem cell23_5736666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_5736666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736666 prefixEnd_5736666 := by exact prefixLift 5736666
  have htrace : WordTrace (prefixWord ++ tailWord_5736666) baseStart_5736666 baseEnd_5736666 := by
    simpa [prefixWord, tailWord_5736666, baseEnd_5736666] using wordTrace_append hprefix tailTrace_5736666
  have hstable : (prefixWord ++ tailWord_5736666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736666).length < 2 ^ (prefixWord ++ tailWord_5736666).sum := by decide
  have hdescent : baseEnd_5736666 < baseStart_5736666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736754 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_5736754 : Nat := 118140960795 + 5736754 * 2 ^ 59
def prefixEnd_5736754 : Nat := 4983230072969 + 3 ^ 40 * 5736754 * 2
def baseEnd_5736754 : Nat := 2945712198603153157292155

theorem tailTrace_5736754 : CollatzResearch.WordTrace tailWord_5736754 prefixEnd_5736754 2945712198603153157292155 := by
  unfold tailWord_5736754
  simp only [CollatzResearch.WordTrace]
  refine ⟨52309151964681873106416329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139491071905818328283776877 52309151964681873106416329)
  ·
    refine ⟨39231863973511404829812247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52309151964681873106416329 39231863973511404829812247)
    ·
      refine ⟨58847795960267107244718371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39231863973511404829812247 58847795960267107244718371)
      ·
        refine ⟨88271693940400660867077557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58847795960267107244718371 88271693940400660867077557)
        ·
          refine ⟨8275471306912561956288521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88271693940400660867077557 8275471306912561956288521)
          ·
            refine ⟨6206603480184421467216391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8275471306912561956288521 6206603480184421467216391)
            ·
              refine ⟨9309905220276632200824587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206603480184421467216391 9309905220276632200824587)
              ·
                refine ⟨13964857830414948301236881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9309905220276632200824587 13964857830414948301236881)
                ·
                  refine ⟨10473643372811211225927661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13964857830414948301236881 10473643372811211225927661)
                  ·
                    refine ⟨3927616264804204209722873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10473643372811211225927661 3927616264804204209722873)
                    ·
                      refine ⟨2945712198603153157292155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927616264804204209722873 2945712198603153157292155)
                      ·
                        rfl

theorem cell23_5736754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_5736754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736754 prefixEnd_5736754 := by exact prefixLift 5736754
  have htrace : WordTrace (prefixWord ++ tailWord_5736754) baseStart_5736754 baseEnd_5736754 := by
    simpa [prefixWord, tailWord_5736754, baseEnd_5736754] using wordTrace_append hprefix tailTrace_5736754
  have hstable : (prefixWord ++ tailWord_5736754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736754).length < 2 ^ (prefixWord ++ tailWord_5736754).sum := by decide
  have hdescent : baseEnd_5736754 < baseStart_5736754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736784 : List Nat := [2, 1, 1, 1, 1, 6, 2, 4, 1, 2, 2]
def baseStart_5736784 : Nat := 118140960795 + 5736784 * 2 ^ 59
def prefixEnd_5736784 : Nat := 4983230072969 + 3 ^ 40 * 5736784 * 2
def baseEnd_5736784 : Nat := 2945727603022788039917017

theorem tailTrace_5736784 : CollatzResearch.WordTrace tailWord_5736784 prefixEnd_5736784 2945727603022788039917017 := by
  unfold tailWord_5736784
  simp only [CollatzResearch.WordTrace]
  refine ⟨104618851024309403774628703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139491801365745871699504937 104618851024309403774628703)
  ·
    refine ⟨156928276536464105661943055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104618851024309403774628703 156928276536464105661943055)
    ·
      refine ⟨235392414804696158492914583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156928276536464105661943055 235392414804696158492914583)
      ·
        refine ⟨353088622207044237739371875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235392414804696158492914583 353088622207044237739371875)
        ·
          refine ⟨529632933310566356609057813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353088622207044237739371875 529632933310566356609057813)
          ·
            refine ⟨24826543748932797966049585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 529632933310566356609057813 24826543748932797966049585)
            ·
              refine ⟨18619907811699598474537189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24826543748932797966049585 18619907811699598474537189)
              ·
                refine ⟨3491232714693674713975723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18619907811699598474537189 3491232714693674713975723)
                ·
                  refine ⟨5236849072040512070963585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491232714693674713975723 5236849072040512070963585)
                  ·
                    refine ⟨3927636804030384053222689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5236849072040512070963585 3927636804030384053222689)
                    ·
                      refine ⟨2945727603022788039917017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927636804030384053222689 2945727603022788039917017)
                      ·
                        rfl

theorem cell23_5736784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 2, 2].length) (baseStart_5736784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736784 prefixEnd_5736784 := by exact prefixLift 5736784
  have htrace : WordTrace (prefixWord ++ tailWord_5736784) baseStart_5736784 baseEnd_5736784 := by
    simpa [prefixWord, tailWord_5736784, baseEnd_5736784] using wordTrace_append hprefix tailTrace_5736784
  have hstable : (prefixWord ++ tailWord_5736784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736784).length < 2 ^ (prefixWord ++ tailWord_5736784).sum := by decide
  have hdescent : baseEnd_5736784 < baseStart_5736784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736798 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5736798 : Nat := 118140960795 + 5736798 * 2 ^ 59
def prefixEnd_5736798 : Nat := 4983230072969 + 3 ^ 40 * 5736798 * 2
def baseEnd_5736798 : Nat := 981911597250650328380651

theorem tailTrace_5736798 : CollatzResearch.WordTrace tailWord_5736798 prefixEnd_5736798 981911597250650328380651 := by
  unfold tailWord_5736798
  simp only [CollatzResearch.WordTrace]
  refine ⟨26154776583821010992533381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139492141780378725293511365 26154776583821010992533381)
  ·
    refine ⟨4904020609466439561100009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26154776583821010992533381 4904020609466439561100009)
    ·
      refine ⟨3678015457099829670825007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4904020609466439561100009 3678015457099829670825007)
      ·
        refine ⟨5517023185649744506237511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678015457099829670825007 5517023185649744506237511)
        ·
          refine ⟨8275534778474616759356267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5517023185649744506237511 8275534778474616759356267)
          ·
            refine ⟨12413302167711925139034401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8275534778474616759356267 12413302167711925139034401)
            ·
              refine ⟨9309976625783943854275801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12413302167711925139034401 9309976625783943854275801)
              ·
                refine ⟨6982482469337957890706851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9309976625783943854275801 6982482469337957890706851)
                ·
                  refine ⟨10473723704006936836060277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982482469337957890706851 10473723704006936836060277)
                  ·
                    refine ⟨981911597250650328380651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10473723704006936836060277 981911597250650328380651)
                    ·
                      rfl

theorem cell23_5736798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5736798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736798 prefixEnd_5736798 := by exact prefixLift 5736798
  have htrace : WordTrace (prefixWord ++ tailWord_5736798) baseStart_5736798 baseEnd_5736798 := by
    simpa [prefixWord, tailWord_5736798, baseEnd_5736798] using wordTrace_append hprefix tailTrace_5736798
  have hstable : (prefixWord ++ tailWord_5736798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736798).length < 2 ^ (prefixWord ++ tailWord_5736798).sum := by decide
  have hdescent : baseEnd_5736798 < baseStart_5736798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736813 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5736813 : Nat := 118140960795 + 5736813 * 2 ^ 59
def prefixEnd_5736813 : Nat := 4983230072969 + 3 ^ 40 * 5736813 * 2
def baseEnd_5736813 : Nat := 2945742493961768426454383

theorem tailTrace_5736813 : CollatzResearch.WordTrace tailWord_5736813 prefixEnd_5736813 2945742493961768426454383 := by
  unfold tailWord_5736813
  simp only [CollatzResearch.WordTrace]
  refine ⟨209238759765513745502063093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139492506510342497001375395 209238759765513745502063093)
  ·
    refine ⟨19616133728016913640818415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209238759765513745502063093 19616133728016913640818415)
    ·
      refine ⟨29424200592025370461227623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19616133728016913640818415 29424200592025370461227623)
      ·
        refine ⟨44136300888038055691841435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29424200592025370461227623 44136300888038055691841435)
        ·
          refine ⟨66204451332057083537762153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44136300888038055691841435 66204451332057083537762153)
          ·
            refine ⟨49653338499042812653321615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66204451332057083537762153 49653338499042812653321615)
            ·
              refine ⟨74480007748564218979982423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49653338499042812653321615 74480007748564218979982423)
              ·
                refine ⟨111720011622846328469973635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74480007748564218979982423 111720011622846328469973635)
                ·
                  refine ⟨167580017434269492704960453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111720011622846328469973635 167580017434269492704960453)
                  ·
                    refine ⟨31421253268925529882180085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167580017434269492704960453 31421253268925529882180085)
                    ·
                      refine ⟨2945742493961768426454383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31421253268925529882180085 2945742493961768426454383)
                      ·
                        rfl

theorem cell23_5736813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5736813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736813 prefixEnd_5736813 := by exact prefixLift 5736813
  have htrace : WordTrace (prefixWord ++ tailWord_5736813) baseStart_5736813 baseEnd_5736813 := by
    simpa [prefixWord, tailWord_5736813, baseEnd_5736813] using wordTrace_append hprefix tailTrace_5736813
  have hstable : (prefixWord ++ tailWord_5736813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736813).length < 2 ^ (prefixWord ++ tailWord_5736813).sum := by decide
  have hdescent : baseEnd_5736813 < baseStart_5736813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736827 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 1, 3, 2]
def baseStart_5736827 : Nat := 118140960795 + 5736827 * 2 ^ 59
def prefixEnd_5736827 : Nat := 4983230072969 + 3 ^ 40 * 5736827 * 2
def baseEnd_5736827 : Nat := 2945749682690931371679319

theorem tailTrace_5736827 : CollatzResearch.WordTrace tailWord_5736827 prefixEnd_5736827 2945749682690931371679319 := by
  unfold tailWord_5736827
  simp only [CollatzResearch.WordTrace]
  refine ⟨209239270387463025893072735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139492846924975350595381823 209239270387463025893072735)
  ·
    refine ⟨313858905581194538839609103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209239270387463025893072735 313858905581194538839609103)
    ·
      refine ⟨470788358371791808259413655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313858905581194538839609103 470788358371791808259413655)
      ·
        refine ⟨706182537557687712389120483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470788358371791808259413655 706182537557687712389120483)
        ·
          refine ⟨1059273806336531568583680725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706182537557687712389120483 1059273806336531568583680725)
          ·
            refine ⟨24826729836012458638680017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1059273806336531568583680725 24826729836012458638680017)
            ·
              refine ⟨18620047377009343979010013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24826729836012458638680017 18620047377009343979010013)
              ·
                refine ⟨6982517766378503992128755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18620047377009343979010013 6982517766378503992128755)
                ·
                  refine ⟨10473776649567755988193133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982517766378503992128755 10473776649567755988193133)
                  ·
                    refine ⟨3927666243587908495572425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10473776649567755988193133 3927666243587908495572425)
                    ·
                      refine ⟨2945749682690931371679319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927666243587908495572425 2945749682690931371679319)
                      ·
                        rfl

theorem cell23_5736827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 3, 2].length) (baseStart_5736827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736827 prefixEnd_5736827 := by exact prefixLift 5736827
  have htrace : WordTrace (prefixWord ++ tailWord_5736827) baseStart_5736827 baseEnd_5736827 := by
    simpa [prefixWord, tailWord_5736827, baseEnd_5736827] using wordTrace_append hprefix tailTrace_5736827
  have hstable : (prefixWord ++ tailWord_5736827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736827).length < 2 ^ (prefixWord ++ tailWord_5736827).sum := by decide
  have hdescent : baseEnd_5736827 < baseStart_5736827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736853 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_5736853 : Nat := 118140960795 + 5736853 * 2 ^ 59
def prefixEnd_5736853 : Nat := 4983230072969 + 3 ^ 40 * 5736853 * 2
def baseEnd_5736853 : Nat := 2945763033187948269954199

theorem tailTrace_5736853 : CollatzResearch.WordTrace tailWord_5736853 prefixEnd_5736853 2945763033187948269954199 := by
  unfold tailWord_5736853
  simp only [CollatzResearch.WordTrace]
  refine ⟨209240218685368832333519213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139493479123579221555679475 209240218685368832333519213)
  ·
    refine ⟨78465082007013312125069705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209240218685368832333519213 78465082007013312125069705)
    ·
      refine ⟨58848811505259984093802279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78465082007013312125069705 58848811505259984093802279)
      ·
        refine ⟨88273217257889976140703419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58848811505259984093802279 88273217257889976140703419)
        ·
          refine ⟨132409825886834964211055129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88273217257889976140703419 132409825886834964211055129)
          ·
            refine ⟨99307369415126223158291347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132409825886834964211055129 99307369415126223158291347)
            ·
              refine ⟨148961054122689334737437021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99307369415126223158291347 148961054122689334737437021)
              ·
                refine ⟨55860395296008500526538883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148961054122689334737437021 55860395296008500526538883)
                ·
                  refine ⟨83790592944012750789808325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55860395296008500526538883 83790592944012750789808325)
                  ·
                    refine ⟨15710736177002390773089061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83790592944012750789808325 15710736177002390773089061)
                    ·
                      refine ⟨2945763033187948269954199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15710736177002390773089061 2945763033187948269954199)
                      ·
                        rfl

theorem cell23_5736853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_5736853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736853 prefixEnd_5736853 := by exact prefixLift 5736853
  have htrace : WordTrace (prefixWord ++ tailWord_5736853) baseStart_5736853 baseEnd_5736853 := by
    simpa [prefixWord, tailWord_5736853, baseEnd_5736853] using wordTrace_append hprefix tailTrace_5736853
  have hstable : (prefixWord ++ tailWord_5736853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736853).length < 2 ^ (prefixWord ++ tailWord_5736853).sum := by decide
  have hdescent : baseEnd_5736853 < baseStart_5736853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736861 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_5736861 : Nat := 118140960795 + 5736861 * 2 ^ 59
def prefixEnd_5736861 : Nat := 4983230072969 + 3 ^ 40 * 5736861 * 2
def baseEnd_5736861 : Nat := 2945767141033184238654163

theorem tailTrace_5736861 : CollatzResearch.WordTrace tailWord_5736861 prefixEnd_5736861 2945767141033184238654163 := by
  unfold tailWord_5736861
  simp only [CollatzResearch.WordTrace]
  refine ⟨209240510469339849699810437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139493673646226566466540291 209240510469339849699810437)
  ·
    refine ⟨39232595713001221818714457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209240510469339849699810437 39232595713001221818714457)
    ·
      refine ⟨29424446784750916364035843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39232595713001221818714457 29424446784750916364035843)
      ·
        refine ⟨44136670177126374546053765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29424446784750916364035843 44136670177126374546053765)
        ·
          refine ⟨8275625658211195227385081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44136670177126374546053765 8275625658211195227385081)
          ·
            refine ⟨6206719243658396420538811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8275625658211195227385081 6206719243658396420538811)
            ·
              refine ⟨9310078865487594630808217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206719243658396420538811 9310078865487594630808217)
              ·
                refine ⟨6982559149115695973106163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9310078865487594630808217 6982559149115695973106163)
                ·
                  refine ⟨10473838723673543959659245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982559149115695973106163 10473838723673543959659245)
                  ·
                    refine ⟨3927689521377578984872217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10473838723673543959659245 3927689521377578984872217)
                    ·
                      refine ⟨2945767141033184238654163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927689521377578984872217 2945767141033184238654163)
                      ·
                        rfl

theorem cell23_5736861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_5736861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736861 prefixEnd_5736861 := by exact prefixLift 5736861
  have htrace : WordTrace (prefixWord ++ tailWord_5736861) baseStart_5736861 baseEnd_5736861 := by
    simpa [prefixWord, tailWord_5736861, baseEnd_5736861] using wordTrace_append hprefix tailTrace_5736861
  have hstable : (prefixWord ++ tailWord_5736861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736861).length < 2 ^ (prefixWord ++ tailWord_5736861).sum := by decide
  have hdescent : baseEnd_5736861 < baseStart_5736861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736863 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 9]
def baseStart_5736863 : Nat := 118140960795 + 5736863 * 2 ^ 59
def prefixEnd_5736863 : Nat := 4983230072969 + 3 ^ 40 * 5736863 * 2
def baseEnd_5736863 : Nat := 327307574221610358981017

theorem tailTrace_5736863 : CollatzResearch.WordTrace tailWord_5736863 prefixEnd_5736863 327307574221610358981017 := by
  unfold tailWord_5736863
  simp only [CollatzResearch.WordTrace]
  refine ⟨209240583415332604041383243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139493722276888402694255495 209240583415332604041383243)
  ·
    refine ⟨313860875122998906062074865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209240583415332604041383243 313860875122998906062074865)
    ·
      refine ⟨235395656342249179546556149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313860875122998906062074865 235395656342249179546556149)
      ·
        refine ⟨22068342782085860582489639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235395656342249179546556149 22068342782085860582489639)
        ·
          refine ⟨33102514173128790873734459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22068342782085860582489639 33102514173128790873734459)
          ·
            refine ⟨49653771259693186310601689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33102514173128790873734459 49653771259693186310601689)
            ·
              refine ⟨37240328444769889732951267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49653771259693186310601689 37240328444769889732951267)
              ·
                refine ⟨55860492667154834599426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37240328444769889732951267 55860492667154834599426901)
                ·
                  refine ⟨327307574221610358981017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55860492667154834599426901 327307574221610358981017)
                  ·
                    rfl

theorem cell23_5736863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 9].length) (baseStart_5736863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736863 prefixEnd_5736863 := by exact prefixLift 5736863
  have htrace : WordTrace (prefixWord ++ tailWord_5736863) baseStart_5736863 baseEnd_5736863 := by
    simpa [prefixWord, tailWord_5736863, baseEnd_5736863] using wordTrace_append hprefix tailTrace_5736863
  have hstable : (prefixWord ++ tailWord_5736863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736863).length < 2 ^ (prefixWord ++ tailWord_5736863).sum := by decide
  have hdescent : baseEnd_5736863 < baseStart_5736863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736927 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 2, 5]
def baseStart_5736927 : Nat := 118140960795 + 5736927 * 2 ^ 59
def prefixEnd_5736927 : Nat := 4983230072969 + 3 ^ 40 * 5736927 * 2
def baseEnd_5736927 : Nat := 981933676918793660142953

theorem tailTrace_5736927 : CollatzResearch.WordTrace tailWord_5736927 prefixEnd_5736927 981933676918793660142953 := by
  unfold tailWord_5736927
  simp only [CollatzResearch.WordTrace]
  refine ⟨209242917687100742971713035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139495278458067161981142023 209242917687100742971713035)
  ·
    refine ⟨313864376530651114457569553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209242917687100742971713035 313864376530651114457569553)
    ·
      refine ⟨235398282397988335843177165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313864376530651114457569553 235398282397988335843177165)
      ·
        refine ⟨88274355899245625941191437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235398282397988335843177165 88274355899245625941191437)
        ·
          refine ⟨33102883462217109727946789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88274355899245625941191437 33102883462217109727946789)
          ·
            refine ⟨6206790649165708073990023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33102883462217109727946789 6206790649165708073990023)
            ·
              refine ⟨9310185973748562110985035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206790649165708073990023 9310185973748562110985035)
              ·
                refine ⟨13965278960622843166477553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9310185973748562110985035 13965278960622843166477553)
                ·
                  refine ⟨10473959220467132374858165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13965278960622843166477553 10473959220467132374858165)
                  ·
                    refine ⟨981933676918793660142953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10473959220467132374858165 981933676918793660142953)
                    ·
                      rfl

theorem cell23_5736927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_5736927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736927 prefixEnd_5736927 := by exact prefixLift 5736927
  have htrace : WordTrace (prefixWord ++ tailWord_5736927) baseStart_5736927 baseEnd_5736927 := by
    simpa [prefixWord, tailWord_5736927, baseEnd_5736927] using wordTrace_append hprefix tailTrace_5736927
  have hstable : (prefixWord ++ tailWord_5736927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736927).length < 2 ^ (prefixWord ++ tailWord_5736927).sum := by decide
  have hdescent : baseEnd_5736927 < baseStart_5736927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736940 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_5736940 : Nat := 118140960795 + 5736940 * 2 ^ 59
def prefixEnd_5736940 : Nat := 4983230072969 + 3 ^ 40 * 5736940 * 2
def baseEnd_5736940 : Nat := 981935902001629809855433

theorem tailTrace_5736940 : CollatzResearch.WordTrace tailWord_5736940 prefixEnd_5736940 981935902001629809855433 := by
  unfold tailWord_5736940
  simp only [CollatzResearch.WordTrace]
  refine ⟨104621695918026823095968137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139495594557369097461290849 104621695918026823095968137)
  ·
    refine ⟨78466271938520117321976103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104621695918026823095968137 78466271938520117321976103)
    ·
      refine ⟨117699407907780175982964155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78466271938520117321976103 117699407907780175982964155)
      ·
        refine ⟨176549111861670263974446233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117699407907780175982964155 176549111861670263974446233)
        ·
          refine ⟨132411833896252697980834675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176549111861670263974446233 132411833896252697980834675)
          ·
            refine ⟨198617750844379046971252013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132411833896252697980834675 198617750844379046971252013)
            ·
              refine ⟨74481656566642142614219505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198617750844379046971252013 74481656566642142614219505)
              ·
                refine ⟨55861242424981606960664629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74481656566642142614219505 55861242424981606960664629)
                ·
                  refine ⟨5236991477342025652562309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55861242424981606960664629 5236991477342025652562309)
                  ·
                    refine ⟨981935902001629809855433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5236991477342025652562309 981935902001629809855433)
                    ·
                      rfl

theorem cell23_5736940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_5736940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736940 prefixEnd_5736940 := by exact prefixLift 5736940
  have htrace : WordTrace (prefixWord ++ tailWord_5736940) baseStart_5736940 baseEnd_5736940 := by
    simpa [prefixWord, tailWord_5736940, baseEnd_5736940] using wordTrace_append hprefix tailTrace_5736940
  have hstable : (prefixWord ++ tailWord_5736940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736940).length < 2 ^ (prefixWord ++ tailWord_5736940).sum := by decide
  have hdescent : baseEnd_5736940 < baseStart_5736940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736957 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_5736957 : Nat := 118140960795 + 5736957 * 2 ^ 59
def prefixEnd_5736957 : Nat := 4983230072969 + 3 ^ 40 * 5736957 * 2
def baseEnd_5736957 : Nat := 981938811725338621017907

theorem tailTrace_5736957 : CollatzResearch.WordTrace tailWord_5736957 prefixEnd_5736957 981938811725338621017907 := by
  unfold tailWord_5736957
  simp only [CollatzResearch.WordTrace]
  refine ⟨209244011876992058095305125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139496007917994705396870083 209244011876992058095305125)
  ·
    refine ⟨39233252226936010892869711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209244011876992058095305125 39233252226936010892869711)
    ·
      refine ⟨58849878340404016339304567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39233252226936010892869711 58849878340404016339304567)
      ·
        refine ⟨88274817510606024508956851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58849878340404016339304567 88274817510606024508956851)
        ·
          refine ⟨132412226265909036763435277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88274817510606024508956851 132412226265909036763435277)
          ·
            refine ⟨49654584849715888786288229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132412226265909036763435277 49654584849715888786288229)
            ·
              refine ⟨9310234659321729147429043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49654584849715888786288229 9310234659321729147429043)
              ·
                refine ⟨13965351988982593721143565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9310234659321729147429043 13965351988982593721143565)
                ·
                  refine ⟨5237006995868472645428837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13965351988982593721143565 5237006995868472645428837)
                  ·
                    refine ⟨981938811725338621017907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5237006995868472645428837 981938811725338621017907)
                    ·
                      rfl

theorem cell23_5736957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_5736957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736957 prefixEnd_5736957 := by exact prefixLift 5736957
  have htrace : WordTrace (prefixWord ++ tailWord_5736957) baseStart_5736957 baseEnd_5736957 := by
    simpa [prefixWord, tailWord_5736957, baseEnd_5736957] using wordTrace_append hprefix tailTrace_5736957
  have hstable : (prefixWord ++ tailWord_5736957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736957).length < 2 ^ (prefixWord ++ tailWord_5736957).sum := by decide
  have hdescent : baseEnd_5736957 < baseStart_5736957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736964 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5736964 : Nat := 118140960795 + 5736964 * 2 ^ 59
def prefixEnd_5736964 : Nat := 4983230072969 + 3 ^ 40 * 5736964 * 2
def baseEnd_5736964 : Nat := 2945820029540597335666189

theorem tailTrace_5736964 : CollatzResearch.WordTrace tailWord_5736964 prefixEnd_5736964 2945820029540597335666189 := by
  unfold tailWord_5736964
  simp only [CollatzResearch.WordTrace]
  refine ⟨104622133593983349145404973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139496178125311132193873297 104622133593983349145404973)
  ·
    refine ⟨39233300097743755929526865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104622133593983349145404973 39233300097743755929526865)
    ·
      refine ⟨29424975073307816947145149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39233300097743755929526865 29424975073307816947145149)
      ·
        refine ⟨11034365652490431355179431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29424975073307816947145149 11034365652490431355179431)
        ·
          refine ⟨16551548478735647032769147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11034365652490431355179431 16551548478735647032769147)
          ·
            refine ⟨24827322718103470549153721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16551548478735647032769147 24827322718103470549153721)
            ·
              refine ⟨18620492038577602911865291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24827322718103470549153721 18620492038577602911865291)
              ·
                refine ⟨27930738057866404367797937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18620492038577602911865291 27930738057866404367797937)
                ·
                  refine ⟨20948053543399803275848453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27930738057866404367797937 20948053543399803275848453)
                  ·
                    refine ⟨3927760039387463114221585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20948053543399803275848453 3927760039387463114221585)
                    ·
                      refine ⟨2945820029540597335666189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927760039387463114221585 2945820029540597335666189)
                      ·
                        rfl

theorem cell23_5736964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5736964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736964 prefixEnd_5736964 := by exact prefixLift 5736964
  have htrace : WordTrace (prefixWord ++ tailWord_5736964) baseStart_5736964 baseEnd_5736964 := by
    simpa [prefixWord, tailWord_5736964, baseEnd_5736964] using wordTrace_append hprefix tailTrace_5736964
  have hstable : (prefixWord ++ tailWord_5736964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736964).length < 2 ^ (prefixWord ++ tailWord_5736964).sum := by decide
  have hdescent : baseEnd_5736964 < baseStart_5736964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736997 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_5736997 : Nat := 118140960795 + 5736997 * 2 ^ 59
def prefixEnd_5736997 : Nat := 4983230072969 + 3 ^ 40 * 5736997 * 2
def baseEnd_5736997 : Nat := 2945836974402195706553537

theorem tailTrace_5736997 : CollatzResearch.WordTrace tailWord_5736997 prefixEnd_5736997 2945836974402195706553537 := by
  unfold tailWord_5736997
  simp only [CollatzResearch.WordTrace]
  refine ⟨209245470796847144926761245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139496980531231429951174163 209245470796847144926761245)
  ·
    refine ⟨78467051548817679347535467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209245470796847144926761245 78467051548817679347535467)
    ·
      refine ⟨117700577323226519021303201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78467051548817679347535467 117700577323226519021303201)
      ·
        refine ⟨88275432992419889265977401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117700577323226519021303201 88275432992419889265977401)
        ·
          refine ⟨66206574744314916949483051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88275432992419889265977401 66206574744314916949483051)
          ·
            refine ⟨99309862116472375424224577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66206574744314916949483051 99309862116472375424224577)
            ·
              refine ⟨74482396587354281568168433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99309862116472375424224577 74482396587354281568168433)
              ·
                refine ⟨55861797440515711176126325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74482396587354281568168433 55861797440515711176126325)
                ·
                  refine ⟨5237043510048347922761843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55861797440515711176126325 5237043510048347922761843)
                  ·
                    refine ⟨7855565265072521884142765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237043510048347922761843 7855565265072521884142765)
                    ·
                      refine ⟨2945836974402195706553537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7855565265072521884142765 2945836974402195706553537)
                      ·
                        rfl

theorem cell23_5736997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_5736997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736997 prefixEnd_5736997 := by exact prefixLift 5736997
  have htrace : WordTrace (prefixWord ++ tailWord_5736997) baseStart_5736997 baseEnd_5736997 := by
    simpa [prefixWord, tailWord_5736997, baseEnd_5736997] using wordTrace_append hprefix tailTrace_5736997
  have hstable : (prefixWord ++ tailWord_5736997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736997).length < 2 ^ (prefixWord ++ tailWord_5736997).sum := by decide
  have hdescent : baseEnd_5736997 < baseStart_5736997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737034 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_5737034 : Nat := 118140960795 + 5737034 * 2 ^ 59
def prefixEnd_5737034 : Nat := 4983230072969 + 3 ^ 40 * 5737034 * 2
def baseEnd_5737034 : Nat := 981951991062137353930289

theorem tailTrace_5737034 : CollatzResearch.WordTrace tailWord_5737034 prefixEnd_5737034 981951991062137353930289 := by
  unfold tailWord_5737034
  simp only [CollatzResearch.WordTrace]
  refine ⟨52311705074428275061464539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139497880198475400163905437 52311705074428275061464539)
  ·
    refine ⟨78467557611642412592196809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52311705074428275061464539 78467557611642412592196809)
    ·
      refine ⟨58850668208731809444147607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78467557611642412592196809 58850668208731809444147607)
      ·
        refine ⟨88276002313097714166221411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58850668208731809444147607 88276002313097714166221411)
        ·
          refine ⟨132414003469646571249332117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88276002313097714166221411 132414003469646571249332117)
          ·
            refine ⟨6206906412639683027312443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132414003469646571249332117 6206906412639683027312443)
            ·
              refine ⟨9310359618959524540968665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6206906412639683027312443 9310359618959524540968665)
              ·
                refine ⟨6982769714219643405726499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9310359618959524540968665 6982769714219643405726499)
                ·
                  refine ⟨10474154571329465108589749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982769714219643405726499 10474154571329465108589749)
                  ·
                    refine ⟨981951991062137353930289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10474154571329465108589749 981951991062137353930289)
                    ·
                      rfl

theorem cell23_5737034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_5737034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737034 prefixEnd_5737034 := by exact prefixLift 5737034
  have htrace : WordTrace (prefixWord ++ tailWord_5737034) baseStart_5737034 baseEnd_5737034 := by
    simpa [prefixWord, tailWord_5737034, baseEnd_5737034] using wordTrace_append hprefix tailTrace_5737034
  have hstable : (prefixWord ++ tailWord_5737034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737034).length < 2 ^ (prefixWord ++ tailWord_5737034).sum := by decide
  have hdescent : baseEnd_5737034 < baseStart_5737034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737057 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_5737057 : Nat := 118140960795 + 5737057 * 2 ^ 59
def prefixEnd_5737057 : Nat := 4983230072969 + 3 ^ 40 * 5737057 * 2
def baseEnd_5737057 : Nat := 2945867783241465471803261

theorem tailTrace_5737057 : CollatzResearch.WordTrace tailWord_5737057 prefixEnd_5737057 2945867783241465471803261 := by
  unfold tailWord_5737057
  simp only [CollatzResearch.WordTrace]
  refine ⟨209247659176629775173945425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139498439451086516782630283 209247659176629775173945425)
  ·
    refine ⟨156935744382472331380459069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209247659176629775173945425 156935744382472331380459069)
    ·
      refine ⟨58850904143427124267672151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156935744382472331380459069 58850904143427124267672151)
      ·
        refine ⟨88276356215140686401508227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58850904143427124267672151 88276356215140686401508227)
        ·
          refine ⟨132414534322711029602262341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88276356215140686401508227 132414534322711029602262341)
          ·
            refine ⟨24827725185508318050424189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132414534322711029602262341 24827725185508318050424189)
            ·
              refine ⟨9310396944565619268909071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24827725185508318050424189 9310396944565619268909071)
              ·
                refine ⟨13965595416848428903363607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9310396944565619268909071 13965595416848428903363607)
                ·
                  refine ⟨20948393125272643355045411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13965595416848428903363607 20948393125272643355045411)
                  ·
                    refine ⟨31422589687908965032568117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20948393125272643355045411 31422589687908965032568117)
                    ·
                      refine ⟨2945867783241465471803261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31422589687908965032568117 2945867783241465471803261)
                      ·
                        rfl

theorem cell23_5737057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_5737057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737057 prefixEnd_5737057 := by exact prefixLift 5737057
  have htrace : WordTrace (prefixWord ++ tailWord_5737057) baseStart_5737057 baseEnd_5737057 := by
    simpa [prefixWord, tailWord_5737057, baseEnd_5737057] using wordTrace_append hprefix tailTrace_5737057
  have hstable : (prefixWord ++ tailWord_5737057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737057).length < 2 ^ (prefixWord ++ tailWord_5737057).sum := by decide
  have hdescent : baseEnd_5737057 < baseStart_5737057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737108 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5737108 : Nat := 118140960795 + 5737108 * 2 ^ 59
def prefixEnd_5737108 : Nat := 4983230072969 + 3 ^ 40 * 5737108 * 2
def baseEnd_5737108 : Nat := 2945893970754844772265527

theorem tailTrace_5737108 : CollatzResearch.WordTrace tailWord_5737108 prefixEnd_5737108 2945893970754844772265527 := by
  unfold tailWord_5737108
  simp only [CollatzResearch.WordTrace]
  refine ⟨104624759649722505442025989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139499679532963340589367985 104624759649722505442025989)
  ·
    refine ⟨19617142434322969770379873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104624759649722505442025989 19617142434322969770379873)
    ·
      refine ⟨14712856825742227327784905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19617142434322969770379873 14712856825742227327784905)
      ·
        refine ⟨11034642619306670495838679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14712856825742227327784905 11034642619306670495838679)
        ·
          refine ⟨16551963928960005743758019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11034642619306670495838679 16551963928960005743758019)
          ·
            refine ⟨24827945893440008615637029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16551963928960005743758019 24827945893440008615637029)
            ·
              refine ⟨4655239855020001615431943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24827945893440008615637029 4655239855020001615431943)
              ·
                refine ⟨6982859782530002423147915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655239855020001615431943 6982859782530002423147915)
                ·
                  refine ⟨10474289673795003634721873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6982859782530002423147915 10474289673795003634721873)
                  ·
                    refine ⟨7855717255346252726041405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10474289673795003634721873 7855717255346252726041405)
                    ·
                      refine ⟨2945893970754844772265527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7855717255346252726041405 2945893970754844772265527)
                      ·
                        rfl

theorem cell23_5737108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5737108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737108 prefixEnd_5737108 := by exact prefixLift 5737108
  have htrace : WordTrace (prefixWord ++ tailWord_5737108) baseStart_5737108 baseEnd_5737108 := by
    simpa [prefixWord, tailWord_5737108, baseEnd_5737108] using wordTrace_append hprefix tailTrace_5737108
  have hstable : (prefixWord ++ tailWord_5737108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737108).length < 2 ^ (prefixWord ++ tailWord_5737108).sum := by decide
  have hdescent : baseEnd_5737108 < baseStart_5737108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737121 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5737121 : Nat := 118140960795 + 5737121 * 2 ^ 59
def prefixEnd_5737121 : Nat := 4983230072969 + 3 ^ 40 * 5737121 * 2
def baseEnd_5737121 : Nat := 2945900646003353221402967

theorem tailTrace_5737121 : CollatzResearch.WordTrace tailWord_5737121 prefixEnd_5737121 2945900646003353221402967 := by
  unfold tailWord_5737121
  simp only [CollatzResearch.WordTrace]
  refine ⟨209249993448397914104275217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139499995632265276069516811 209249993448397914104275217)
  ·
    refine ⟨156937495086298435578206413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209249993448397914104275217 156937495086298435578206413)
    ·
      refine ⟨58851560657361913341827405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156937495086298435578206413 58851560657361913341827405)
      ·
        refine ⟨22069335246510717503185277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58851560657361913341827405 22069335246510717503185277)
        ·
          refine ⟨8276000717441519063694479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22069335246510717503185277 8276000717441519063694479)
          ·
            refine ⟨12414001076162278595541719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8276000717441519063694479 12414001076162278595541719)
            ·
              refine ⟨18621001614243417893312579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12414001076162278595541719 18621001614243417893312579)
              ·
                refine ⟨27931502421365126839968869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18621001614243417893312579 27931502421365126839968869)
                ·
                  refine ⟨5237156704005961282494163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27931502421365126839968869 5237156704005961282494163)
                  ·
                    refine ⟨7855735056008941923741245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237156704005961282494163 7855735056008941923741245)
                    ·
                      refine ⟨2945900646003353221402967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7855735056008941923741245 2945900646003353221402967)
                      ·
                        rfl

theorem cell23_5737121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5737121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737121 prefixEnd_5737121 := by exact prefixLift 5737121
  have htrace : WordTrace (prefixWord ++ tailWord_5737121) baseStart_5737121 baseEnd_5737121 := by
    simpa [prefixWord, tailWord_5737121, baseEnd_5737121] using wordTrace_append hprefix tailTrace_5737121
  have hstable : (prefixWord ++ tailWord_5737121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737121).length < 2 ^ (prefixWord ++ tailWord_5737121).sum := by decide
  have hdescent : baseEnd_5737121 < baseStart_5737121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737164 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5737164 : Nat := 118140960795 + 5737164 * 2 ^ 59
def prefixEnd_5737164 : Nat := 4983230072969 + 3 ^ 40 * 5737164 * 2
def baseEnd_5737164 : Nat := 2945922725671496553165269

theorem tailTrace_5737164 : CollatzResearch.WordTrace tailWord_5737164 prefixEnd_5737164 2945922725671496553165269 := by
  unfold tailWord_5737164
  simp only [CollatzResearch.WordTrace]
  refine ⟨104625780893621066224045273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139501041191494754965393697 104625780893621066224045273)
  ·
    refine ⟨78469335670215799668033955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104625780893621066224045273 78469335670215799668033955)
    ·
      refine ⟨117704003505323699502050933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78469335670215799668033955 117704003505323699502050933)
      ·
        refine ⟨11034750328624096828317275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117704003505323699502050933 11034750328624096828317275)
        ·
          refine ⟨16552125492936145242475913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11034750328624096828317275 16552125492936145242475913)
          ·
            refine ⟨12414094119702108931856935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16552125492936145242475913 12414094119702108931856935)
            ·
              refine ⟨18621141179553163397785403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12414094119702108931856935 18621141179553163397785403)
              ·
                refine ⟨27931711769329745096678105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18621141179553163397785403 27931711769329745096678105)
                ·
                  refine ⟨20948783826997308822508579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27931711769329745096678105 20948783826997308822508579)
                  ·
                    refine ⟨31423175740495963233762869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20948783826997308822508579 31423175740495963233762869)
                    ·
                      refine ⟨2945922725671496553165269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31423175740495963233762869 2945922725671496553165269)
                      ·
                        rfl

theorem cell23_5737164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5737164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737164 prefixEnd_5737164 := by exact prefixLift 5737164
  have htrace : WordTrace (prefixWord ++ tailWord_5737164) baseStart_5737164 baseEnd_5737164 := by
    simpa [prefixWord, tailWord_5737164, baseEnd_5737164] using wordTrace_append hprefix tailTrace_5737164
  have hstable : (prefixWord ++ tailWord_5737164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737164).length < 2 ^ (prefixWord ++ tailWord_5737164).sum := by decide
  have hdescent : baseEnd_5737164 < baseStart_5737164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737237 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_5737237 : Nat := 118140960795 + 5737237 * 2 ^ 59
def prefixEnd_5737237 : Nat := 4983230072969 + 3 ^ 40 * 5737237 * 2
def baseEnd_5737237 : Nat := 2945960209759274767552433

theorem tailTrace_5737237 : CollatzResearch.WordTrace tailWord_5737237 prefixEnd_5737237 2945960209759274767552433 := by
  unfold tailWord_5737237
  simp only [CollatzResearch.WordTrace]
  refine ⟨209254224315977665915497965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139502816210651777276998643 209254224315977665915497965)
  ·
    refine ⟨78470334118491624718311737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209254224315977665915497965 78470334118491624718311737)
    ·
      refine ⟨58852750588868718538733803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78470334118491624718311737 58852750588868718538733803)
      ·
        refine ⟨88279125883303077808100705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58852750588868718538733803 88279125883303077808100705)
        ·
          refine ⟨66209344412477308356075529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88279125883303077808100705 66209344412477308356075529)
          ·
            refine ⟨49657008309357981267056647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66209344412477308356075529 49657008309357981267056647)
            ·
              refine ⟨74485512464036971900584971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49657008309357981267056647 74485512464036971900584971)
              ·
                refine ⟨111728268696055457850877457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74485512464036971900584971 111728268696055457850877457)
                ·
                  refine ⟨83796201522041593388158093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111728268696055457850877457 83796201522041593388158093)
                  ·
                    refine ⟨31423575570765597520559285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83796201522041593388158093 31423575570765597520559285)
                    ·
                      refine ⟨2945960209759274767552433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31423575570765597520559285 2945960209759274767552433)
                      ·
                        rfl

theorem cell23_5737237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_5737237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737237 prefixEnd_5737237 := by exact prefixLift 5737237
  have htrace : WordTrace (prefixWord ++ tailWord_5737237) baseStart_5737237 baseEnd_5737237 := by
    simpa [prefixWord, tailWord_5737237, baseEnd_5737237] using wordTrace_append hprefix tailTrace_5737237
  have hstable : (prefixWord ++ tailWord_5737237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737237).length < 2 ^ (prefixWord ++ tailWord_5737237).sum := by decide
  have hdescent : baseEnd_5737237 < baseStart_5737237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737308 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 6]
def baseStart_5737308 : Nat := 118140960795 + 5737308 * 2 ^ 59
def prefixEnd_5737308 : Nat := 4983230072969 + 3 ^ 40 * 5737308 * 2
def baseEnd_5737308 : Nat := 327332962987304887751623

theorem tailTrace_5737308 : CollatzResearch.WordTrace tailWord_5737308 prefixEnd_5737308 327332962987304887751623 := by
  unfold tailWord_5737308
  simp only [CollatzResearch.WordTrace]
  refine ⟨104628406949360222520666289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139504542599146963360888385 104628406949360222520666289)
  ·
    refine ⟨78471305212020166890499717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104628406949360222520666289 78471305212020166890499717)
    ·
      refine ⟨14713369727253781291968697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78471305212020166890499717 14713369727253781291968697)
      ·
        refine ⟨11035027295440335968976523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14713369727253781291968697 11035027295440335968976523)
        ·
          refine ⟨16552540943160503953464785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11035027295440335968976523 16552540943160503953464785)
          ·
            refine ⟨12414405707370377965098589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16552540943160503953464785 12414405707370377965098589)
            ·
              refine ⟨4655402140263891736911971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12414405707370377965098589 4655402140263891736911971)
              ·
                refine ⟨6983103210395837605367957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655402140263891736911971 6983103210395837605367957)
                ·
                  refine ⟨327332962987304887751623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6983103210395837605367957 327332962987304887751623)
                  ·
                    rfl

theorem cell23_5737308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_5737308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737308 prefixEnd_5737308 := by exact prefixLift 5737308
  have htrace : WordTrace (prefixWord ++ tailWord_5737308) baseStart_5737308 baseEnd_5737308 := by
    simpa [prefixWord, tailWord_5737308, baseEnd_5737308] using wordTrace_append hprefix tailTrace_5737308
  have hstable : (prefixWord ++ tailWord_5737308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737308).length < 2 ^ (prefixWord ++ tailWord_5737308).sum := by decide
  have hdescent : baseEnd_5737308 < baseStart_5737308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737341 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_5737341 : Nat := 118140960795 + 5737341 * 2 ^ 59
def prefixEnd_5737341 : Nat := 4983230072969 + 3 ^ 40 * 5737341 * 2
def baseEnd_5737341 : Nat := 2946013611747342360651955

theorem tailTrace_5737341 : CollatzResearch.WordTrace tailWord_5737341 prefixEnd_5737341 2946013611747342360651955 := by
  unfold tailWord_5737341
  simp only [CollatzResearch.WordTrace]
  refine ⟨209258017507600891677283877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139505345005067261118189251 209258017507600891677283877)
  ·
    refine ⟨39235878282675167189490727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209258017507600891677283877 39235878282675167189490727)
    ·
      refine ⟨58853817424012750784236091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39235878282675167189490727 58853817424012750784236091)
      ·
        refine ⟨88280726136019126176354137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58853817424012750784236091 88280726136019126176354137)
        ·
          refine ⟨66210544602014344632265603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88280726136019126176354137 66210544602014344632265603)
          ·
            refine ⟨99315816903021516948398405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66210544602014344632265603 99315816903021516948398405)
            ·
              refine ⟨18621715669316534427824701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99315816903021516948398405 18621715669316534427824701)
              ·
                refine ⟨6983143375993700410434263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18621715669316534427824701 6983143375993700410434263)
                ·
                  refine ⟨10474715063990550615651395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6983143375993700410434263 10474715063990550615651395)
                  ·
                    refine ⟨15712072595985825923477093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10474715063990550615651395 15712072595985825923477093)
                    ·
                      refine ⟨2946013611747342360651955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15712072595985825923477093 2946013611747342360651955)
                      ·
                        rfl

theorem cell23_5737341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_5737341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737341 prefixEnd_5737341 := by exact prefixLift 5737341
  have htrace : WordTrace (prefixWord ++ tailWord_5737341) baseStart_5737341 baseEnd_5737341 := by
    simpa [prefixWord, tailWord_5737341, baseEnd_5737341] using wordTrace_append hprefix tailTrace_5737341
  have hstable : (prefixWord ++ tailWord_5737341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737341).length < 2 ^ (prefixWord ++ tailWord_5737341).sum := by decide
  have hdescent : baseEnd_5737341 < baseStart_5737341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737351 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 4, 4]
def baseStart_5737351 : Nat := 118140960795 + 5737351 * 2 ^ 59
def prefixEnd_5737351 : Nat := 4983230072969 + 3 ^ 40 * 5737351 * 2
def baseEnd_5737351 : Nat := 982006248851295773842303

theorem tailTrace_5737351 : CollatzResearch.WordTrace tailWord_5737351 prefixEnd_5737351 982006248851295773842303 := by
  unfold tailWord_5737351
  simp only [CollatzResearch.WordTrace]
  refine ⟨209258382237564663385147907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139505588158376442256765271 209258382237564663385147907)
  ·
    refine ⟨313887573356346995077721861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209258382237564663385147907 313887573356346995077721861)
    ·
      refine ⟨58853920004315061577072849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313887573356346995077721861 58853920004315061577072849)
      ·
        refine ⟨44140440003236296182804637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58853920004315061577072849 44140440003236296182804637)
        ·
          refine ⟨16552665001213611068551739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44140440003236296182804637 16552665001213611068551739)
          ·
            refine ⟨24828997501820416602827609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16552665001213611068551739 24828997501820416602827609)
            ·
              refine ⟨18621748126365312452120707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24828997501820416602827609 18621748126365312452120707)
              ·
                refine ⟨27932622189547968678181061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18621748126365312452120707 27932622189547968678181061)
                ·
                  refine ⟨5237366660540244127158949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27932622189547968678181061 5237366660540244127158949)
                  ·
                    refine ⟨982006248851295773842303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5237366660540244127158949 982006248851295773842303)
                    ·
                      rfl

theorem cell23_5737351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_5737351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737351 prefixEnd_5737351 := by exact prefixLift 5737351
  have htrace : WordTrace (prefixWord ++ tailWord_5737351) baseStart_5737351 baseEnd_5737351 := by
    simpa [prefixWord, tailWord_5737351, baseEnd_5737351] using wordTrace_append hprefix tailTrace_5737351
  have hstable : (prefixWord ++ tailWord_5737351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737351).length < 2 ^ (prefixWord ++ tailWord_5737351).sum := by decide
  have hdescent : baseEnd_5737351 < baseStart_5737351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737352 : List Nat := [2, 1, 3, 3, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5737352 : Nat := 118140960795 + 5737352 * 2 ^ 59
def prefixEnd_5737352 : Nat := 4983230072969 + 3 ^ 40 * 5737352 * 2
def baseEnd_5737352 : Nat := 2946019260034541817614405

theorem tailTrace_5737352 : CollatzResearch.WordTrace tailWord_5737352 prefixEnd_5737352 2946019260034541817614405 := by
  unfold tailWord_5737352
  simp only [CollatzResearch.WordTrace]
  refine ⟨104629209355280520277967155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139505612473707360370622873 104629209355280520277967155)
  ·
    refine ⟨156943814032920780416950733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104629209355280520277967155 156943814032920780416950733)
    ·
      refine ⟨58853930262345292656356525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156943814032920780416950733 58853930262345292656356525)
      ·
        refine ⟨22070223848379484746133697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58853930262345292656356525 22070223848379484746133697)
        ·
          refine ⟨16552667886284613559600273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22070223848379484746133697 16552667886284613559600273)
          ·
            refine ⟨12414500914713460169700205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16552667886284613559600273 12414500914713460169700205)
            ·
              refine ⟨4655437843017547563637577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12414500914713460169700205 4655437843017547563637577)
              ·
                refine ⟨3491578382263160672728183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655437843017547563637577 3491578382263160672728183)
                ·
                  refine ⟨5237367573394741009092275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491578382263160672728183 5237367573394741009092275)
                  ·
                    refine ⟨7856051360092111513638413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237367573394741009092275 7856051360092111513638413)
                    ·
                      refine ⟨2946019260034541817614405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856051360092111513638413 2946019260034541817614405)
                      ·
                        rfl

theorem cell23_5737352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5737352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737352 prefixEnd_5737352 := by exact prefixLift 5737352
  have htrace : WordTrace (prefixWord ++ tailWord_5737352) baseStart_5737352 baseEnd_5737352 := by
    simpa [prefixWord, tailWord_5737352, baseEnd_5737352] using wordTrace_append hprefix tailTrace_5737352
  have hstable : (prefixWord ++ tailWord_5737352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737352).length < 2 ^ (prefixWord ++ tailWord_5737352).sum := by decide
  have hdescent : baseEnd_5737352 < baseStart_5737352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737378 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_5737378 : Nat := 118140960795 + 5737378 * 2 ^ 59
def prefixEnd_5737378 : Nat := 4983230072969 + 3 ^ 40 * 5737378 * 2
def baseEnd_5737378 : Nat := 2946032610531558715889285

theorem tailTrace_5737378 : CollatzResearch.WordTrace tailWord_5737378 prefixEnd_5737378 2946032610531558715889285 := by
  unfold tailWord_5737378
  simp only [CollatzResearch.WordTrace]
  refine ⟨52314841752116711749095197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139506244672311231330920525 52314841752116711749095197)
  ·
    refine ⟨19618065657043766905910699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52314841752116711749095197 19618065657043766905910699)
    ·
      refine ⟨29427098485565650358866049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19618065657043766905910699 29427098485565650358866049)
      ·
        refine ⟨22070323864174237769149537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29427098485565650358866049 22070323864174237769149537)
        ·
          refine ⟨16552742898130678326862153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22070323864174237769149537 16552742898130678326862153)
          ·
            refine ⟨12414557173598008745146615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16552742898130678326862153 12414557173598008745146615)
            ·
              refine ⟨18621835760397013117719923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12414557173598008745146615 18621835760397013117719923)
              ·
                refine ⟨27932753640595519676579885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18621835760397013117719923 27932753640595519676579885)
                ·
                  refine ⟨10474782615223319878717457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27932753640595519676579885 10474782615223319878717457)
                  ·
                    refine ⟨7856086961417489909038093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10474782615223319878717457 7856086961417489909038093)
                    ·
                      refine ⟨2946032610531558715889285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856086961417489909038093 2946032610531558715889285)
                      ·
                        rfl

theorem cell23_5737378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_5737378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737378 prefixEnd_5737378 := by exact prefixLift 5737378
  have htrace : WordTrace (prefixWord ++ tailWord_5737378) baseStart_5737378 baseEnd_5737378 := by
    simpa [prefixWord, tailWord_5737378, baseEnd_5737378] using wordTrace_append hprefix tailTrace_5737378
  have hstable : (prefixWord ++ tailWord_5737378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737378).length < 2 ^ (prefixWord ++ tailWord_5737378).sum := by decide
  have hdescent : baseEnd_5737378 < baseStart_5737378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737391 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 3]
def baseStart_5737391 : Nat := 118140960795 + 5737391 * 2 ^ 59
def prefixEnd_5737391 : Nat := 4983230072969 + 3 ^ 40 * 5737391 * 2
def baseEnd_5737391 : Nat := 2946039285780067165026725

theorem tailTrace_5737391 : CollatzResearch.WordTrace tailWord_5737391 prefixEnd_5737391 2946039285780067165026725 := by
  unfold tailWord_5737391
  simp only [CollatzResearch.WordTrace]
  refine ⟨209259841157419750216604027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139506560771613166811069351 209259841157419750216604027)
  ·
    refine ⟨313889761736129625324906041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209259841157419750216604027 313889761736129625324906041)
    ·
      refine ⟨235417321302097218993679531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313889761736129625324906041 235417321302097218993679531)
      ·
        refine ⟨353125981953145828490519297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235417321302097218993679531 353125981953145828490519297)
        ·
          refine ⟨264844486464859371367889473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353125981953145828490519297 264844486464859371367889473)
          ·
            refine ⟨198633364848644528525917105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264844486464859371367889473 198633364848644528525917105)
            ·
              refine ⟨148975023636483396394437829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198633364848644528525917105 148975023636483396394437829)
              ·
                refine ⟨27932816931840636823957093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148975023636483396394437829 27932816931840636823957093)
                ·
                  refine ⟨5237403174720119404491955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27932816931840636823957093 5237403174720119404491955)
                  ·
                    refine ⟨7856104762080179106737933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237403174720119404491955 7856104762080179106737933)
                    ·
                      refine ⟨2946039285780067165026725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856104762080179106737933 2946039285780067165026725)
                      ·
                        rfl

theorem cell23_5737391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 3].length) (baseStart_5737391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737391 prefixEnd_5737391 := by exact prefixLift 5737391
  have htrace : WordTrace (prefixWord ++ tailWord_5737391) baseStart_5737391 baseEnd_5737391 := by
    simpa [prefixWord, tailWord_5737391, baseEnd_5737391] using wordTrace_append hprefix tailTrace_5737391
  have hstable : (prefixWord ++ tailWord_5737391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737391).length < 2 ^ (prefixWord ++ tailWord_5737391).sum := by decide
  have hdescent : baseEnd_5737391 < baseStart_5737391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737398 : List Nat := [5, 1, 4, 1, 12]
def baseStart_5737398 : Nat := 118140960795 + 5737398 * 2 ^ 59
def prefixEnd_5737398 : Nat := 4983230072969 + 3 ^ 40 * 5737398 * 2
def baseEnd_5737398 : Nat := 4041211083874689489217

theorem tailTrace_5737398 : CollatzResearch.WordTrace tailWord_5737398 prefixEnd_5737398 4041211083874689489217 := by
  unfold tailWord_5737398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078756029274649400756803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139506730978929593608072565 13078756029274649400756803)
  ·
    refine ⟨19618134043911974101135205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13078756029274649400756803 19618134043911974101135205)
    ·
      refine ⟨3678400133233495143962851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19618134043911974101135205 3678400133233495143962851)
      ·
        refine ⟨5517600199850242715944277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678400133233495143962851 5517600199850242715944277)
        ·
          refine ⟨4041211083874689489217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5517600199850242715944277 4041211083874689489217)
          ·
            rfl

theorem cell23_5737398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 12].length) (baseStart_5737398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737398 prefixEnd_5737398 := by exact prefixLift 5737398
  have htrace : WordTrace (prefixWord ++ tailWord_5737398) baseStart_5737398 baseEnd_5737398 := by
    simpa [prefixWord, tailWord_5737398, baseEnd_5737398] using wordTrace_append hprefix tailTrace_5737398
  have hstable : (prefixWord ++ tailWord_5737398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737398).length < 2 ^ (prefixWord ++ tailWord_5737398).sum := by decide
  have hdescent : baseEnd_5737398 < baseStart_5737398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737408 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 2, 1, 3]
def baseStart_5737408 : Nat := 118140960795 + 5737408 * 2 ^ 59
def prefixEnd_5737408 : Nat := 4983230072969 + 3 ^ 40 * 5737408 * 2
def baseEnd_5737408 : Nat := 2946048014951193598514147

theorem tailTrace_5737408 : CollatzResearch.WordTrace tailWord_5737408 prefixEnd_5737408 2946048014951193598514147 := by
  unfold tailWord_5737408
  simp only [CollatzResearch.WordTrace]
  refine ⟨104630230599179081059986439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139506974132238774746648585 104630230599179081059986439)
  ·
    refine ⟨156945345898768621589979659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104630230599179081059986439 156945345898768621589979659)
    ·
      refine ⟨235418018848152932384969489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156945345898768621589979659 235418018848152932384969489)
      ·
        refine ⟨176563514136114699288727117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235418018848152932384969489 176563514136114699288727117)
        ·
          refine ⟨66211317801043012233272669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176563514136114699288727117 66211317801043012233272669)
          ·
            refine ⟨24829244175391129587477251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66211317801043012233272669 24829244175391129587477251)
            ·
              refine ⟨37243866263086694381215877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24829244175391129587477251 37243866263086694381215877)
              ·
                refine ⟨6983224924328755196477977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37243866263086694381215877 6983224924328755196477977)
                ·
                  refine ⟨5237418693246566397358483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6983224924328755196477977 5237418693246566397358483)
                  ·
                    refine ⟨7856128039869849596037725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237418693246566397358483 7856128039869849596037725)
                    ·
                      refine ⟨2946048014951193598514147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856128039869849596037725 2946048014951193598514147)
                      ·
                        rfl

theorem cell23_5737408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 2, 1, 3].length) (baseStart_5737408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737408 prefixEnd_5737408 := by exact prefixLift 5737408
  have htrace : WordTrace (prefixWord ++ tailWord_5737408) baseStart_5737408 baseEnd_5737408 := by
    simpa [prefixWord, tailWord_5737408, baseEnd_5737408] using wordTrace_append hprefix tailTrace_5737408
  have hstable : (prefixWord ++ tailWord_5737408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737408).length < 2 ^ (prefixWord ++ tailWord_5737408).sum := by decide
  have hdescent : baseEnd_5737408 < baseStart_5737408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737448 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_5737448 : Nat := 118140960795 + 5737448 * 2 ^ 59
def prefixEnd_5737448 : Nat := 4983230072969 + 3 ^ 40 * 5737448 * 2
def baseEnd_5737448 : Nat := 2946068554177373442013963

theorem tailTrace_5737448 : CollatzResearch.WordTrace tailWord_5737448 prefixEnd_5737448 2946068554177373442013963 := by
  unfold tailWord_5737448
  simp only [CollatzResearch.WordTrace]
  refine ⟨104630960059106624475714499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139507946745475499300952665 104630960059106624475714499)
  ·
    refine ⟨156946440088659936713571749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104630960059106624475714499 156946440088659936713571749)
    ·
      refine ⟨29427457516623738133794703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156946440088659936713571749 29427457516623738133794703)
      ·
        refine ⟨44141186274935607200692055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29427457516623738133794703 44141186274935607200692055)
        ·
          refine ⟨66211779412403410801038083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44141186274935607200692055 66211779412403410801038083)
          ·
            refine ⟨99317669118605116201557125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66211779412403410801038083 99317669118605116201557125)
            ·
              refine ⟨18622062959738459287791961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99317669118605116201557125 18622062959738459287791961)
              ·
                refine ⟨13966547219803844465843971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18622062959738459287791961 13966547219803844465843971)
                ·
                  refine ⟨20949820829705766698765957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13966547219803844465843971 20949820829705766698765957)
                  ·
                    refine ⟨3928091405569831256018617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20949820829705766698765957 3928091405569831256018617)
                    ·
                      refine ⟨2946068554177373442013963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3928091405569831256018617 2946068554177373442013963)
                      ·
                        rfl

theorem cell23_5737448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_5737448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737448 prefixEnd_5737448 := by exact prefixLift 5737448
  have htrace : WordTrace (prefixWord ++ tailWord_5737448) baseStart_5737448 baseEnd_5737448 := by
    simpa [prefixWord, tailWord_5737448, baseEnd_5737448] using wordTrace_append hprefix tailTrace_5737448
  have hstable : (prefixWord ++ tailWord_5737448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737448).length < 2 ^ (prefixWord ++ tailWord_5737448).sum := by decide
  have hdescent : baseEnd_5737448 < baseStart_5737448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737505 : List Nat := [1, 2, 3, 2, 3, 3, 1, 3, 5]
def baseStart_5737505 : Nat := 118140960795 + 5737505 * 2 ^ 59
def prefixEnd_5737505 : Nat := 4983230072969 + 3 ^ 40 * 5737505 * 2
def baseEnd_5737505 : Nat := 327344202508297746555689

theorem tailTrace_5737505 : CollatzResearch.WordTrace tailWord_5737505 prefixEnd_5737505 327344202508297746555689 := by
  unfold tailWord_5737505
  simp only [CollatzResearch.WordTrace]
  refine ⟨209263999079006747686253969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139509332719337831790835979 209263999079006747686253969)
  ·
    refine ⟨156947999309255060764690477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209263999079006747686253969 156947999309255060764690477)
    ·
      refine ⟨58855499740970647786758929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156947999309255060764690477 58855499740970647786758929)
      ·
        refine ⟨44141624805727985840069197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58855499740970647786758929 44141624805727985840069197)
        ·
          refine ⟨16553109302147994690025949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44141624805727985840069197 16553109302147994690025949)
          ·
            refine ⟨6207415988305498008759731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16553109302147994690025949 6207415988305498008759731)
            ·
              refine ⟨9311123982458247013139597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6207415988305498008759731 9311123982458247013139597)
              ·
                refine ⟨3491671493421842629927349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9311123982458247013139597 3491671493421842629927349)
                ·
                  refine ⟨327344202508297746555689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3491671493421842629927349 327344202508297746555689)
                  ·
                    rfl

theorem cell23_5737505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 3, 5].length) (baseStart_5737505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737505 prefixEnd_5737505 := by exact prefixLift 5737505
  have htrace : WordTrace (prefixWord ++ tailWord_5737505) baseStart_5737505 baseEnd_5737505 := by
    simpa [prefixWord, tailWord_5737505, baseEnd_5737505] using wordTrace_append hprefix tailTrace_5737505
  have hstable : (prefixWord ++ tailWord_5737505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737505).length < 2 ^ (prefixWord ++ tailWord_5737505).sum := by decide
  have hdescent : baseEnd_5737505 < baseStart_5737505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737518 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_5737518 : Nat := 118140960795 + 5737518 * 2 ^ 59
def prefixEnd_5737518 : Nat := 4983230072969 + 3 ^ 40 * 5737518 * 2
def baseEnd_5737518 : Nat := 982034832607729389379547

theorem tailTrace_5737518 : CollatzResearch.WordTrace tailWord_5737518 prefixEnd_5737518 982034832607729389379547 := by
  unfold tailWord_5737518
  simp only [CollatzResearch.WordTrace]
  refine ⟨26158059153494956363309651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139509648818639767270984805 26158059153494956363309651)
  ·
    refine ⟨39237088730242434544964477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26158059153494956363309651 39237088730242434544964477)
    ·
      refine ⟨14713908273840912954361679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39237088730242434544964477 14713908273840912954361679)
      ·
        refine ⟨22070862410761369431542519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14713908273840912954361679 22070862410761369431542519)
        ·
          refine ⟨33106293616142054147313779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22070862410761369431542519 33106293616142054147313779)
          ·
            refine ⟨49659440424213081220970669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33106293616142054147313779 49659440424213081220970669)
            ·
              refine ⟨18622290159079905457864001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49659440424213081220970669 18622290159079905457864001)
              ·
                refine ⟨13966717619309929093398001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18622290159079905457864001 13966717619309929093398001)
                ·
                  refine ⟨10475038214482446820048501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13966717619309929093398001 10475038214482446820048501)
                  ·
                    refine ⟨982034832607729389379547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10475038214482446820048501 982034832607729389379547)
                    ·
                      rfl

theorem cell23_5737518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_5737518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737518 prefixEnd_5737518 := by exact prefixLift 5737518
  have htrace : WordTrace (prefixWord ++ tailWord_5737518) baseStart_5737518 baseEnd_5737518 := by
    simpa [prefixWord, tailWord_5737518, baseEnd_5737518] using wordTrace_append hprefix tailTrace_5737518
  have hstable : (prefixWord ++ tailWord_5737518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737518).length < 2 ^ (prefixWord ++ tailWord_5737518).sum := by decide
  have hdescent : baseEnd_5737518 < baseStart_5737518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737541 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_5737541 : Nat := 118140960795 + 5737541 * 2 ^ 59
def prefixEnd_5737541 : Nat := 4983230072969 + 3 ^ 40 * 5737541 * 2
def baseEnd_5737541 : Nat := 2946116307878241578151035

theorem tailTrace_5737541 : CollatzResearch.WordTrace tailWord_5737541 prefixEnd_5737541 2946116307878241578151035 := by
  unfold tailWord_5737541
  simp only [CollatzResearch.WordTrace]
  refine ⟨209265312106876325834564477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139510208071250883889709651 209265312106876325834564477)
  ·
    refine ⟨78474492040078622187961679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209265312106876325834564477 78474492040078622187961679)
    ·
      refine ⟨117711738060117933281942519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78474492040078622187961679 117711738060117933281942519)
      ·
        refine ⟨176567607090176899922913779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117711738060117933281942519 176567607090176899922913779)
        ·
          refine ⟨264851410635265349884370669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176567607090176899922913779 264851410635265349884370669)
          ·
            refine ⟨99319278988224506206639001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264851410635265349884370669 99319278988224506206639001)
            ·
              refine ⟨74489459241168379654979251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99319278988224506206639001 74489459241168379654979251)
              ·
                refine ⟨111734188861752569482468877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74489459241168379654979251 111734188861752569482468877)
                ·
                  refine ⟨41900320823157213555925829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111734188861752569482468877 41900320823157213555925829)
                  ·
                    refine ⟨7856310154341977541736093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41900320823157213555925829 7856310154341977541736093)
                    ·
                      refine ⟨2946116307878241578151035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856310154341977541736093 2946116307878241578151035)
                      ·
                        rfl

theorem cell23_5737541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_5737541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737541 prefixEnd_5737541 := by exact prefixLift 5737541
  have htrace : WordTrace (prefixWord ++ tailWord_5737541) baseStart_5737541 baseEnd_5737541 := by
    simpa [prefixWord, tailWord_5737541, baseEnd_5737541] using wordTrace_append hprefix tailTrace_5737541
  have hstable : (prefixWord ++ tailWord_5737541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737541).length < 2 ^ (prefixWord ++ tailWord_5737541).sum := by decide
  have hdescent : baseEnd_5737541 < baseStart_5737541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737578 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 6]
def baseStart_5737578 : Nat := 118140960795 + 5737578 * 2 ^ 59
def prefixEnd_5737578 : Nat := 4983230072969 + 3 ^ 40 * 5737578 * 2
def baseEnd_5737578 : Nat := 327348367406939770376485

theorem tailTrace_5737578 : CollatzResearch.WordTrace tailWord_5737578 prefixEnd_5737578 327348367406939770376485 := by
  unfold tailWord_5737578
  simp only [CollatzResearch.WordTrace]
  refine ⟨52316665401935570288415347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139511107738494854102440925 52316665401935570288415347)
  ·
    refine ⟨78474998102903355432623021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52316665401935570288415347 78474998102903355432623021)
    ·
      refine ⟨29428124288588758287233633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78474998102903355432623021 29428124288588758287233633)
      ·
        refine ⟨22071093216441568715425225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29428124288588758287233633 22071093216441568715425225)
        ·
          refine ⟨16553319912331176536568919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22071093216441568715425225 16553319912331176536568919)
          ·
            refine ⟨24829979868496764804853379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16553319912331176536568919 24829979868496764804853379)
            ·
              refine ⟨37244969802745147207280069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24829979868496764804853379 37244969802745147207280069)
              ·
                refine ⟨6983431838014715101365013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37244969802745147207280069 6983431838014715101365013)
                ·
                  refine ⟨327348367406939770376485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6983431838014715101365013 327348367406939770376485)
                  ·
                    rfl

theorem cell23_5737578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_5737578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737578 prefixEnd_5737578 := by exact prefixLift 5737578
  have htrace : WordTrace (prefixWord ++ tailWord_5737578) baseStart_5737578 baseEnd_5737578 := by
    simpa [prefixWord, tailWord_5737578, baseEnd_5737578] using wordTrace_append hprefix tailTrace_5737578
  have hstable : (prefixWord ++ tailWord_5737578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737578).length < 2 ^ (prefixWord ++ tailWord_5737578).sum := by decide
  have hdescent : baseEnd_5737578 < baseStart_5737578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737582 : List Nat := [4, 1, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_5737582 : Nat := 118140960795 + 5737582 * 2 ^ 59
def prefixEnd_5737582 : Nat := 4983230072969 + 3 ^ 40 * 5737582 * 2
def baseEnd_5737582 : Nat := 982045786861691972579449

theorem tailTrace_5737582 : CollatzResearch.WordTrace tailWord_5737582 prefixEnd_5737582 982045786861691972579449 := by
  unfold tailWord_5737582
  simp only [CollatzResearch.WordTrace]
  refine ⟨26158350937465973729600875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139511204999818526557871333 26158350937465973729600875)
  ·
    refine ⟨39237526406198960594401313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26158350937465973729600875 39237526406198960594401313)
    ·
      refine ⟨29428144804649220445800985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39237526406198960594401313 29428144804649220445800985)
      ·
        refine ⟨22071108603486915334350739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29428144804649220445800985 22071108603486915334350739)
        ·
          refine ⟨33106662905230373001526109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22071108603486915334350739 33106662905230373001526109)
          ·
            refine ⟨12414998589461389875572291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33106662905230373001526109 12414998589461389875572291)
            ·
              refine ⟨18622497884192084813358437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12414998589461389875572291 18622497884192084813358437)
              ·
                refine ⟨3491718353286015902504707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18622497884192084813358437 3491718353286015902504707)
                ·
                  refine ⟨5237577529929023853757061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491718353286015902504707 5237577529929023853757061)
                  ·
                    refine ⟨982045786861691972579449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5237577529929023853757061 982045786861691972579449)
                    ·
                      rfl

theorem cell23_5737582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_5737582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737582 prefixEnd_5737582 := by exact prefixLift 5737582
  have htrace : WordTrace (prefixWord ++ tailWord_5737582) baseStart_5737582 baseEnd_5737582 := by
    simpa [prefixWord, tailWord_5737582, baseEnd_5737582] using wordTrace_append hprefix tailTrace_5737582
  have hstable : (prefixWord ++ tailWord_5737582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737582).length < 2 ^ (prefixWord ++ tailWord_5737582).sum := by decide
  have hdescent : baseEnd_5737582 < baseStart_5737582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737591 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 5, 5]
def baseStart_5737591 : Nat := 118140960795 + 5737591 * 2 ^ 59
def prefixEnd_5737591 : Nat := 4983230072969 + 3 ^ 40 * 5737591 * 2
def baseEnd_5737591 : Nat := 982047327303655460841935

theorem tailTrace_5737591 : CollatzResearch.WordTrace tailWord_5737591 prefixEnd_5737591 982047327303655460841935 := by
  unfold tailWord_5737591
  simp only [CollatzResearch.WordTrace]
  refine ⟨209267135756695184373884627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139511423837796789582589751 209267135756695184373884627)
  ·
    refine ⟨313900703635042776560826941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209267135756695184373884627 313900703635042776560826941)
    ·
      refine ⟨117712763863141041210310103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313900703635042776560826941 117712763863141041210310103)
      ·
        refine ⟨176569145794711561815465155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117712763863141041210310103 176569145794711561815465155)
        ·
          refine ⟨264853718692067342723197733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176569145794711561815465155 264853718692067342723197733)
          ·
            refine ⟨49660072254762626760599575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264853718692067342723197733 49660072254762626760599575)
            ·
              refine ⟨74490108382143940140899363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49660072254762626760599575 74490108382143940140899363)
              ·
                refine ⟨111735162573215910211349045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74490108382143940140899363 111735162573215910211349045)
                ·
                  refine ⟨10475171491238991582313973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111735162573215910211349045 10475171491238991582313973)
                  ·
                    refine ⟨982047327303655460841935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10475171491238991582313973 982047327303655460841935)
                    ·
                      rfl

theorem cell23_5737591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_5737591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737591 prefixEnd_5737591 := by exact prefixLift 5737591
  have htrace : WordTrace (prefixWord ++ tailWord_5737591) baseStart_5737591 baseEnd_5737591 := by
    simpa [prefixWord, tailWord_5737591, baseEnd_5737591] using wordTrace_append hprefix tailTrace_5737591
  have hstable : (prefixWord ++ tailWord_5737591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737591).length < 2 ^ (prefixWord ++ tailWord_5737591).sum := by decide
  have hdescent : baseEnd_5737591 < baseStart_5737591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737621 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_5737621 : Nat := 118140960795 + 5737621 * 2 ^ 59
def prefixEnd_5737621 : Nat := 4983230072969 + 3 ^ 40 * 5737621 * 2
def baseEnd_5737621 : Nat := 982052462110200421716889

theorem tailTrace_5737621 : CollatzResearch.WordTrace tailWord_5737621 prefixEnd_5737621 982052462110200421716889 := by
  unfold tailWord_5737621
  simp only [CollatzResearch.WordTrace]
  refine ⟨209268229946586499497476717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139512153297724332998317811 209268229946586499497476717)
  ·
    refine ⟨78475586229969937311553769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209268229946586499497476717 78475586229969937311553769)
    ·
      refine ⟨58856689672477452983665327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78475586229969937311553769 58856689672477452983665327)
      ·
        refine ⟨88285034508716179475497991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58856689672477452983665327 88285034508716179475497991)
        ·
          refine ⟨132427551763074269213246987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88285034508716179475497991 132427551763074269213246987)
          ·
            refine ⟨198641327644611403819870481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132427551763074269213246987 198641327644611403819870481)
            ·
              refine ⟨148980995733458552864902861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198641327644611403819870481 148980995733458552864902861)
              ·
                refine ⟨55867873400046957324338573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148980995733458552864902861 55867873400046957324338573)
                ·
                  refine ⟨20950452525017608996626965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55867873400046957324338573 20950452525017608996626965)
                  ·
                    refine ⟨982052462110200421716889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20950452525017608996626965 982052462110200421716889)
                    ·
                      rfl

theorem cell23_5737621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_5737621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737621 prefixEnd_5737621 := by exact prefixLift 5737621
  have htrace : WordTrace (prefixWord ++ tailWord_5737621) baseStart_5737621 baseEnd_5737621 := by
    simpa [prefixWord, tailWord_5737621, baseEnd_5737621] using wordTrace_append hprefix tailTrace_5737621
  have hstable : (prefixWord ++ tailWord_5737621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737621).length < 2 ^ (prefixWord ++ tailWord_5737621).sum := by decide
  have hdescent : baseEnd_5737621 < baseStart_5737621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737639 : List Nat := [1, 1, 6, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5737639 : Nat := 118140960795 + 5737639 * 2 ^ 59
def prefixEnd_5737639 : Nat := 4983230072969 + 3 ^ 40 * 5737639 * 2
def baseEnd_5737639 : Nat := 2946166628982382194725585

theorem tailTrace_5737639 : CollatzResearch.WordTrace tailWord_5737639 prefixEnd_5737639 2946166628982382194725585 := by
  unfold tailWord_5737639
  simp only [CollatzResearch.WordTrace]
  refine ⟨209268886460521288571631971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139512590973680859047754647 209268886460521288571631971)
  ·
    refine ⟨313903329690781932857447957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209268886460521288571631971 313903329690781932857447957)
    ·
      refine ⟨14714218579255403102692873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 313903329690781932857447957 14714218579255403102692873)
      ·
        refine ⟨11035663934441552327019655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14714218579255403102692873 11035663934441552327019655)
        ·
          refine ⟨16553495901662328490529483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11035663934441552327019655 16553495901662328490529483)
          ·
            refine ⟨24830243852493492735794225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16553495901662328490529483 24830243852493492735794225)
            ·
              refine ⟨18622682889370119551845669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24830243852493492735794225 18622682889370119551845669)
              ·
                refine ⟨3491753041756897415971063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18622682889370119551845669 3491753041756897415971063)
                ·
                  refine ⟨5237629562635346123956595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491753041756897415971063 5237629562635346123956595)
                  ·
                    refine ⟨7856444343953019185934893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237629562635346123956595 7856444343953019185934893)
                    ·
                      refine ⟨2946166628982382194725585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856444343953019185934893 2946166628982382194725585)
                      ·
                        rfl

theorem cell23_5737639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5737639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737639 prefixEnd_5737639 := by exact prefixLift 5737639
  have htrace : WordTrace (prefixWord ++ tailWord_5737639) baseStart_5737639 baseEnd_5737639 := by
    simpa [prefixWord, tailWord_5737639, baseEnd_5737639] using wordTrace_append hprefix tailTrace_5737639
  have hstable : (prefixWord ++ tailWord_5737639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737639).length < 2 ^ (prefixWord ++ tailWord_5737639).sum := by decide
  have hdescent : baseEnd_5737639 < baseStart_5737639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737662 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_5737662 : Nat := 118140960795 + 5737662 * 2 ^ 59
def prefixEnd_5737662 : Nat := 4983230072969 + 3 ^ 40 * 5737662 * 2
def baseEnd_5737662 : Nat := 2946178439037435604737979

theorem tailTrace_5737662 : CollatzResearch.WordTrace tailWord_5737662 prefixEnd_5737662 2946178439037435604737979 := by
  unfold tailWord_5737662
  simp only [CollatzResearch.WordTrace]
  refine ⟨26158715667429745437464905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139513150226291975666479493 26158715667429745437464905)
  ·
    refine ⟨19619036750572309078098679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26158715667429745437464905 19619036750572309078098679)
    ·
      refine ⟨29428555125858463617148019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19619036750572309078098679 29428555125858463617148019)
      ·
        refine ⟨44142832688787695425722029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29428555125858463617148019 44142832688787695425722029)
        ·
          refine ⟨16553562258295385784645761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44142832688787695425722029 16553562258295385784645761)
          ·
            refine ⟨12415171693721539338484321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16553562258295385784645761 12415171693721539338484321)
            ·
              refine ⟨9311378770291154503863241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12415171693721539338484321 9311378770291154503863241)
              ·
                refine ⟨6983534077718365877897431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9311378770291154503863241 6983534077718365877897431)
                ·
                  refine ⟨10475301116577548816846147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6983534077718365877897431 10475301116577548816846147)
                  ·
                    refine ⟨15712951674866323225269221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10475301116577548816846147 15712951674866323225269221)
                    ·
                      refine ⟨2946178439037435604737979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15712951674866323225269221 2946178439037435604737979)
                      ·
                        rfl

theorem cell23_5737662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_5737662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737662 prefixEnd_5737662 := by exact prefixLift 5737662
  have htrace : WordTrace (prefixWord ++ tailWord_5737662) baseStart_5737662 baseEnd_5737662 := by
    simpa [prefixWord, tailWord_5737662, baseEnd_5737662] using wordTrace_append hprefix tailTrace_5737662
  have hstable : (prefixWord ++ tailWord_5737662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737662).length < 2 ^ (prefixWord ++ tailWord_5737662).sum := by decide
  have hdescent : baseEnd_5737662 < baseStart_5737662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737671 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_5737671 : Nat := 118140960795 + 5737671 * 2 ^ 59
def prefixEnd_5737671 : Nat := 4983230072969 + 3 ^ 40 * 5737671 * 2
def baseEnd_5737671 : Nat := 2946183060363326069525437

theorem tailTrace_5737671 : CollatzResearch.WordTrace tailWord_5737671 prefixEnd_5737671 2946183060363326069525437 := by
  unfold tailWord_5737671
  simp only [CollatzResearch.WordTrace]
  refine ⟨209270053596405358036796867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139513369064270238691197911 209270053596405358036796867)
  ·
    refine ⟨313905080394608037055195301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209270053596405358036796867 313905080394608037055195301)
    ·
      refine ⟨58857202573989006947849119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313905080394608037055195301 58857202573989006947849119)
      ·
        refine ⟨88285803860983510421773679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58857202573989006947849119 88285803860983510421773679)
        ·
          refine ⟨132428705791475265632660519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88285803860983510421773679 132428705791475265632660519)
          ·
            refine ⟨198643058687212898448990779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132428705791475265632660519 198643058687212898448990779)
            ·
              refine ⟨297964588030819347673486169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198643058687212898448990779 297964588030819347673486169)
              ·
                refine ⟨223473441023114510755114627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297964588030819347673486169 223473441023114510755114627)
                ·
                  refine ⟨335210161534671766132671941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223473441023114510755114627 335210161534671766132671941)
                  ·
                    refine ⟨62851905287750956149875989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 335210161534671766132671941 62851905287750956149875989)
                    ·
                      refine ⟨2946183060363326069525437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62851905287750956149875989 2946183060363326069525437)
                      ·
                        rfl

theorem cell23_5737671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_5737671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737671 prefixEnd_5737671 := by exact prefixLift 5737671
  have htrace : WordTrace (prefixWord ++ tailWord_5737671) baseStart_5737671 baseEnd_5737671 := by
    simpa [prefixWord, tailWord_5737671, baseEnd_5737671] using wordTrace_append hprefix tailTrace_5737671
  have hstable : (prefixWord ++ tailWord_5737671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737671).length < 2 ^ (prefixWord ++ tailWord_5737671).sum := by decide
  have hdescent : baseEnd_5737671 < baseStart_5737671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737681 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 9]
def baseStart_5737681 : Nat := 118140960795 + 5737681 * 2 ^ 59
def prefixEnd_5737681 : Nat := 4983230072969 + 3 ^ 40 * 5737681 * 2
def baseEnd_5737681 : Nat := 982062731723290343466797

theorem tailTrace_5737681 : CollatzResearch.WordTrace tailWord_5737681 prefixEnd_5737681 982062731723290343466797 := by
  unfold tailWord_5737681
  simp only [CollatzResearch.WordTrace]
  refine ⟨209270418326369129744660897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139513612217579419829773931 209270418326369129744660897)
  ·
    refine ⟨156952813744776847308495673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209270418326369129744660897 156952813744776847308495673)
    ·
      refine ⟨117714610308582635481371755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156952813744776847308495673 117714610308582635481371755)
      ·
        refine ⟨176571915462873953222057633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117714610308582635481371755 176571915462873953222057633)
        ·
          refine ⟨132428936597155464916543225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176571915462873953222057633 132428936597155464916543225)
          ·
            refine ⟨99321702447866598687407419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132428936597155464916543225 99321702447866598687407419)
            ·
              refine ⟨148982553671799898031111129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99321702447866598687407419 148982553671799898031111129)
              ·
                refine ⟨111736915253849923523333347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148982553671799898031111129 111736915253849923523333347)
                ·
                  refine ⟨167605372880774885285000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111736915253849923523333347 167605372880774885285000021)
                  ·
                    refine ⟨982062731723290343466797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 167605372880774885285000021 982062731723290343466797)
                    ·
                      rfl

theorem cell23_5737681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_5737681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737681 prefixEnd_5737681 := by exact prefixLift 5737681
  have htrace : WordTrace (prefixWord ++ tailWord_5737681) baseStart_5737681 baseEnd_5737681 := by
    simpa [prefixWord, tailWord_5737681, baseEnd_5737681] using wordTrace_append hprefix tailTrace_5737681
  have hstable : (prefixWord ++ tailWord_5737681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737681).length < 2 ^ (prefixWord ++ tailWord_5737681).sum := by decide
  have hdescent : baseEnd_5737681 < baseStart_5737681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737691 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5]
def baseStart_5737691 : Nat := 118140960795 + 5737691 * 2 ^ 59
def prefixEnd_5737691 : Nat := 4983230072969 + 3 ^ 40 * 5737691 * 2
def baseEnd_5737691 : Nat := 2946193329976415991275345

theorem tailTrace_5737691 : CollatzResearch.WordTrace tailWord_5737691 prefixEnd_5737691 2946193329976415991275345 := by
  unfold tailWord_5737691
  simp only [CollatzResearch.WordTrace]
  refine ⟨209270783056332901452524927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139513855370888600968349951 209270783056332901452524927)
  ·
    refine ⟨313906174584499352178787391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209270783056332901452524927 313906174584499352178787391)
    ·
      refine ⟨470859261876749028268181087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313906174584499352178787391 470859261876749028268181087)
      ·
        refine ⟨706288892815123542402271631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470859261876749028268181087 706288892815123542402271631)
        ·
          refine ⟨1059433339222685313603407447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706288892815123542402271631 1059433339222685313603407447)
          ·
            refine ⟨1589150008834027970405111171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059433339222685313603407447 1589150008834027970405111171)
            ·
              refine ⟨2383725013251041955607666757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589150008834027970405111171 2383725013251041955607666757)
              ·
                refine ⟨446948439984570366676437517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2383725013251041955607666757 446948439984570366676437517)
                ·
                  refine ⟨167605664994213887503664069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446948439984570366676437517 167605664994213887503664069)
                  ·
                    refine ⟨31426062186415103906937013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167605664994213887503664069 31426062186415103906937013)
                    ·
                      refine ⟨2946193329976415991275345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31426062186415103906937013 2946193329976415991275345)
                      ·
                        rfl

theorem cell23_5737691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_5737691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737691 prefixEnd_5737691 := by exact prefixLift 5737691
  have htrace : WordTrace (prefixWord ++ tailWord_5737691) baseStart_5737691 baseEnd_5737691 := by
    simpa [prefixWord, tailWord_5737691, baseEnd_5737691] using wordTrace_append hprefix tailTrace_5737691
  have hstable : (prefixWord ++ tailWord_5737691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737691).length < 2 ^ (prefixWord ++ tailWord_5737691).sum := by decide
  have hdescent : baseEnd_5737691 < baseStart_5737691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737695 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 3]
def baseStart_5737695 : Nat := 118140960795 + 5737695 * 2 ^ 59
def prefixEnd_5737695 : Nat := 4983230072969 + 3 ^ 40 * 5737695 * 2
def baseEnd_5737695 : Nat := 2946195383899033975625327

theorem tailTrace_5737695 : CollatzResearch.WordTrace tailWord_5737695 prefixEnd_5737695 2946195383899033975625327 := by
  unfold tailWord_5737695
  simp only [CollatzResearch.WordTrace]
  refine ⟨209270928948318410135670539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139513952632212273423780359 209270928948318410135670539)
  ·
    refine ⟨313906393422477615203505809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209270928948318410135670539 313906393422477615203505809)
    ·
      refine ⟨235429795066858211402629357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313906393422477615203505809 235429795066858211402629357)
      ·
        refine ⟨88286173150071829275986009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235429795066858211402629357 88286173150071829275986009)
        ·
          refine ⟨66214629862553871956989507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88286173150071829275986009 66214629862553871956989507)
          ·
            refine ⟨99321944793830807935484261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66214629862553871956989507 99321944793830807935484261)
            ·
              refine ⟨18622864648843276487903299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99321944793830807935484261 18622864648843276487903299)
              ·
                refine ⟨27934296973264914731854949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18622864648843276487903299 27934296973264914731854949)
                ·
                  refine ⟨5237680682487171512222803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27934296973264914731854949 5237680682487171512222803)
                  ·
                    refine ⟨7856521023730757268334205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237680682487171512222803 7856521023730757268334205)
                    ·
                      refine ⟨2946195383899033975625327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856521023730757268334205 2946195383899033975625327)
                      ·
                        rfl

theorem cell23_5737695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_5737695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737695 prefixEnd_5737695 := by exact prefixLift 5737695
  have htrace : WordTrace (prefixWord ++ tailWord_5737695) baseStart_5737695 baseEnd_5737695 := by
    simpa [prefixWord, tailWord_5737695, baseEnd_5737695] using wordTrace_append hprefix tailTrace_5737695
  have hstable : (prefixWord ++ tailWord_5737695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737695).length < 2 ^ (prefixWord ++ tailWord_5737695).sum := by decide
  have hdescent : baseEnd_5737695 < baseStart_5737695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737696 : List Nat := [2, 1, 1, 3, 1, 5, 3, 2, 1, 2, 2]
def baseStart_5737696 : Nat := 118140960795 + 5737696 * 2 ^ 59
def prefixEnd_5737696 : Nat := 4983230072969 + 3 ^ 40 * 5737696 * 2
def baseEnd_5737696 : Nat := 2946195897379688471712823

theorem tailTrace_5737696 : CollatzResearch.WordTrace tailWord_5737696 prefixEnd_5737696 2946195897379688471712823 := by
  unfold tailWord_5737696
  simp only [CollatzResearch.WordTrace]
  refine ⟨104635482710657393653228471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139513976947543191537637961 104635482710657393653228471)
  ·
    refine ⟨156953224065986090479842707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104635482710657393653228471 156953224065986090479842707)
    ·
      refine ⟨235429836098979135719764061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156953224065986090479842707 235429836098979135719764061)
      ·
        refine ⟨88286188537117175894911523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235429836098979135719764061 88286188537117175894911523)
        ·
          refine ⟨132429282805675763842367285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88286188537117175894911523 132429282805675763842367285)
          ·
            refine ⟨12415245263032102860221933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132429282805675763842367285 12415245263032102860221933)
            ·
              refine ⟨4655716973637038572583225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12415245263032102860221933 4655716973637038572583225)
              ·
                refine ⟨3491787730227778929437419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4655716973637038572583225 3491787730227778929437419)
                ·
                  refine ⟨5237681595341668394156129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3491787730227778929437419 5237681595341668394156129)
                  ·
                    refine ⟨3928261196506251295617097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5237681595341668394156129 3928261196506251295617097)
                    ·
                      refine ⟨2946195897379688471712823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3928261196506251295617097 2946195897379688471712823)
                      ·
                        rfl

theorem cell23_5737696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_5737696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737696 prefixEnd_5737696 := by exact prefixLift 5737696
  have htrace : WordTrace (prefixWord ++ tailWord_5737696) baseStart_5737696 baseEnd_5737696 := by
    simpa [prefixWord, tailWord_5737696, baseEnd_5737696] using wordTrace_append hprefix tailTrace_5737696
  have hstable : (prefixWord ++ tailWord_5737696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737696).length < 2 ^ (prefixWord ++ tailWord_5737696).sum := by decide
  have hdescent : baseEnd_5737696 < baseStart_5737696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737716 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5737716 : Nat := 118140960795 + 5737716 * 2 ^ 59
def prefixEnd_5737716 : Nat := 4983230072969 + 3 ^ 40 * 5737716 * 2
def baseEnd_5737716 : Nat := 2946206166992778393462731

theorem tailTrace_5737716 : CollatzResearch.WordTrace tailWord_5737716 prefixEnd_5737716 2946206166992778393462731 := by
  unfold tailWord_5737716
  simp only [CollatzResearch.WordTrace]
  refine ⟨104635847440621165361092501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139514463254161553814790001 104635847440621165361092501)
  ·
    refine ⟨4904805348779117126301211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104635847440621165361092501 4904805348779117126301211)
    ·
      refine ⟨7357208023168675689451817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4904805348779117126301211 7357208023168675689451817)
      ·
        refine ⟨5517906017376506767088863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7357208023168675689451817 5517906017376506767088863)
        ·
          refine ⟨8276859026064760150633295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5517906017376506767088863 8276859026064760150633295)
          ·
            refine ⟨12415288539097140225949943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8276859026064760150633295 12415288539097140225949943)
            ·
              refine ⟨18622932808645710338924915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12415288539097140225949943 18622932808645710338924915)
              ·
                refine ⟨27934399212968565508387373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18622932808645710338924915 27934399212968565508387373)
                ·
                  refine ⟨10475399704863212065645265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27934399212968565508387373 10475399704863212065645265)
                  ·
                    refine ⟨7856549778647409049233949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10475399704863212065645265 7856549778647409049233949)
                    ·
                      refine ⟨2946206166992778393462731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856549778647409049233949 2946206166992778393462731)
                      ·
                        rfl

theorem cell23_5737716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5737716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737716 prefixEnd_5737716 := by exact prefixLift 5737716
  have htrace : WordTrace (prefixWord ++ tailWord_5737716) baseStart_5737716 baseEnd_5737716 := by
    simpa [prefixWord, tailWord_5737716, baseEnd_5737716] using wordTrace_append hprefix tailTrace_5737716
  have hstable : (prefixWord ++ tailWord_5737716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737716).length < 2 ^ (prefixWord ++ tailWord_5737716).sum := by decide
  have hdescent : baseEnd_5737716 < baseStart_5737716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737718 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5737718 : Nat := 118140960795 + 5737718 * 2 ^ 59
def prefixEnd_5737718 : Nat := 4983230072969 + 3 ^ 40 * 5737718 * 2
def baseEnd_5737718 : Nat := 2946207193954087385637721

theorem tailTrace_5737718 : CollatzResearch.WordTrace tailWord_5737718 prefixEnd_5737718 2946207193954087385637721 := by
  unfold tailWord_5737718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13079485489202192816484863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139514511884823390042505205 13079485489202192816484863)
  ·
    refine ⟨19619228233803289224727295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13079485489202192816484863 19619228233803289224727295)
    ·
      refine ⟨29428842350704933837090943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19619228233803289224727295 29428842350704933837090943)
      ·
        refine ⟨44143263526057400755636415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29428842350704933837090943 44143263526057400755636415)
        ·
          refine ⟨66214895289086101133454623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44143263526057400755636415 66214895289086101133454623)
          ·
            refine ⟨99322342933629151700181935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66214895289086101133454623 99322342933629151700181935)
            ·
              refine ⟨148983514400443727550272903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99322342933629151700181935 148983514400443727550272903)
              ·
                refine ⟨223475271600665591325409355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148983514400443727550272903 223475271600665591325409355)
                ·
                  refine ⟨335212907400998386988114033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223475271600665591325409355 335212907400998386988114033)
                  ·
                    refine ⟨251409680550748790241085525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 335212907400998386988114033 251409680550748790241085525)
                    ·
                      refine ⟨2946207193954087385637721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 251409680550748790241085525 2946207193954087385637721)
                      ·
                        rfl

theorem cell23_5737718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5737718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737718 prefixEnd_5737718 := by exact prefixLift 5737718
  have htrace : WordTrace (prefixWord ++ tailWord_5737718) baseStart_5737718 baseEnd_5737718 := by
    simpa [prefixWord, tailWord_5737718, baseEnd_5737718] using wordTrace_append hprefix tailTrace_5737718
  have hstable : (prefixWord ++ tailWord_5737718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737718).length < 2 ^ (prefixWord ++ tailWord_5737718).sum := by decide
  have hdescent : baseEnd_5737718 < baseStart_5737718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737739 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 1, 3, 2]
def baseStart_5737739 : Nat := 118140960795 + 5737739 * 2 ^ 59
def prefixEnd_5737739 : Nat := 4983230072969 + 3 ^ 40 * 5737739 * 2
def baseEnd_5737739 : Nat := 2946217977047831803475125

theorem tailTrace_5737739 : CollatzResearch.WordTrace tailWord_5737739 prefixEnd_5737739 2946217977047831803475125 := by
  unfold tailWord_5737739
  simp only [CollatzResearch.WordTrace]
  refine ⟨209272533760159005650272271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139515022506772670433514847 209272533760159005650272271)
  ·
    refine ⟨313908800640238508475408407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209272533760159005650272271 313908800640238508475408407)
    ·
      refine ⟨470863200960357762713112611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313908800640238508475408407 470863200960357762713112611)
      ·
        refine ⟨706294801440536644069668917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470863200960357762713112611 706294801440536644069668917)
        ·
          refine ⟨66215137635050310381531461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 706294801440536644069668917 66215137635050310381531461)
          ·
            refine ⟨12415338306571933196537149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66215137635050310381531461 12415338306571933196537149)
            ·
              refine ⟨4655751864964474948701431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12415338306571933196537149 4655751864964474948701431)
              ·
                refine ⟨6983627797446712423052147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655751864964474948701431 6983627797446712423052147)
                ·
                  refine ⟨10475441696170068634578221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6983627797446712423052147 10475441696170068634578221)
                  ·
                    refine ⟨3928290636063775737966833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10475441696170068634578221 3928290636063775737966833)
                    ·
                      refine ⟨2946217977047831803475125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3928290636063775737966833 2946217977047831803475125)
                      ·
                        rfl

theorem cell23_5737739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 3, 2].length) (baseStart_5737739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737739 prefixEnd_5737739 := by exact prefixLift 5737739
  have htrace : WordTrace (prefixWord ++ tailWord_5737739) baseStart_5737739 baseEnd_5737739 := by
    simpa [prefixWord, tailWord_5737739, baseEnd_5737739] using wordTrace_append hprefix tailTrace_5737739
  have hstable : (prefixWord ++ tailWord_5737739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737739).length < 2 ^ (prefixWord ++ tailWord_5737739).sum := by decide
  have hdescent : baseEnd_5737739 < baseStart_5737739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737765 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_5737765 : Nat := 118140960795 + 5737765 * 2 ^ 59
def prefixEnd_5737765 : Nat := 4983230072969 + 3 ^ 40 * 5737765 * 2
def baseEnd_5737765 : Nat := 2946231327544848701750005

theorem tailTrace_5737765 : CollatzResearch.WordTrace tailWord_5737765 prefixEnd_5737765 2946231327544848701750005 := by
  unfold tailWord_5737765
  simp only [CollatzResearch.WordTrace]
  refine ⟨209273482058064812090718749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139515654705376541393812499 209273482058064812090718749)
  ·
    refine ⟨78477555771774304534019531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209273482058064812090718749 78477555771774304534019531)
    ·
      refine ⟨117716333657661456801029297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78477555771774304534019531 117716333657661456801029297)
      ·
        refine ⟨88287250243246092600771973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117716333657661456801029297 88287250243246092600771973)
        ·
          refine ⟨16553859420608642362644745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88287250243246092600771973 16553859420608642362644745)
          ·
            refine ⟨12415394565456481771983559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16553859420608642362644745 12415394565456481771983559)
            ·
              refine ⟨18623091848184722657975339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12415394565456481771983559 18623091848184722657975339)
              ·
                refine ⟨27934637772277083986963009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18623091848184722657975339 27934637772277083986963009)
                ·
                  refine ⟨20950978329207812990222257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27934637772277083986963009 20950978329207812990222257)
                  ·
                    refine ⟨15713233746905859742666693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20950978329207812990222257 15713233746905859742666693)
                    ·
                      refine ⟨2946231327544848701750005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15713233746905859742666693 2946231327544848701750005)
                      ·
                        rfl

theorem cell23_5737765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_5737765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737765 prefixEnd_5737765 := by exact prefixLift 5737765
  have htrace : WordTrace (prefixWord ++ tailWord_5737765) baseStart_5737765 baseEnd_5737765 := by
    simpa [prefixWord, tailWord_5737765, baseEnd_5737765] using wordTrace_append hprefix tailTrace_5737765
  have hstable : (prefixWord ++ tailWord_5737765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737765).length < 2 ^ (prefixWord ++ tailWord_5737765).sum := by decide
  have hdescent : baseEnd_5737765 < baseStart_5737765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737892 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_5737892 : Nat := 118140960795 + 5737892 * 2 ^ 59
def prefixEnd_5737892 : Nat := 4983230072969 + 3 ^ 40 * 5737892 * 2
def baseEnd_5737892 : Nat := 2946296539587969704861921

theorem tailTrace_5737892 : CollatzResearch.WordTrace tailWord_5737892 prefixEnd_5737892 2946296539587969704861921 := by
  unfold tailWord_5737892
  simp only [CollatzResearch.WordTrace]
  refine ⟨104639057064302356390295965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139518742752403141853727953 104639057064302356390295965)
  ·
    refine ⟨39239646399113383646360987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104639057064302356390295965 39239646399113383646360987)
    ·
      refine ⟨58859469598670075469541481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39239646399113383646360987 58859469598670075469541481)
      ·
        refine ⟨44144602199002556602156111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58859469598670075469541481 44144602199002556602156111)
        ·
          refine ⟨66216903298503834903234167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44144602199002556602156111 66216903298503834903234167)
          ·
            refine ⟨99325354947755752354851251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66216903298503834903234167 99325354947755752354851251)
            ·
              refine ⟨148988032421633628532276877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99325354947755752354851251 148988032421633628532276877)
              ·
                refine ⟨55870512158112610699603829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148988032421633628532276877 55870512158112610699603829)
                ·
                  refine ⟨5237860514823057253087859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55870512158112610699603829 5237860514823057253087859)
                  ·
                    refine ⟨7856790772234585879631789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5237860514823057253087859 7856790772234585879631789)
                    ·
                      refine ⟨2946296539587969704861921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856790772234585879631789 2946296539587969704861921)
                      ·
                        rfl

theorem cell23_5737892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_5737892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737892 prefixEnd_5737892 := by exact prefixLift 5737892
  have htrace : WordTrace (prefixWord ++ tailWord_5737892) baseStart_5737892 baseEnd_5737892 := by
    simpa [prefixWord, tailWord_5737892, baseEnd_5737892] using wordTrace_append hprefix tailTrace_5737892
  have hstable : (prefixWord ++ tailWord_5737892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737892).length < 2 ^ (prefixWord ++ tailWord_5737892).sum := by decide
  have hdescent : baseEnd_5737892 < baseStart_5737892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737896 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5737896 : Nat := 118140960795 + 5737896 * 2 ^ 59
def prefixEnd_5737896 : Nat := 4983230072969 + 3 ^ 40 * 5737896 * 2
def baseEnd_5737896 : Nat := 2946298593510587689211903

theorem tailTrace_5737896 : CollatzResearch.WordTrace tailWord_5737896 prefixEnd_5737896 2946298593510587689211903 := by
  unfold tailWord_5737896
  simp only [CollatzResearch.WordTrace]
  refine ⟨104639130010295110731868771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139518840013726814309158361 104639130010295110731868771)
  ·
    refine ⟨156958695015442666097803157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104639130010295110731868771 156958695015442666097803157)
    ·
      refine ⟨7357438828848874973334523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156958695015442666097803157 7357438828848874973334523)
      ·
        refine ⟨11036158243273312460001785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7357438828848874973334523 11036158243273312460001785)
        ·
          refine ⟨8277118682454984345001339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11036158243273312460001785 8277118682454984345001339)
          ·
            refine ⟨12415678023682476517502009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8277118682454984345001339 12415678023682476517502009)
            ·
              refine ⟨9311758517761857388126507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12415678023682476517502009 9311758517761857388126507)
              ·
                refine ⟨13967637776642786082189761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9311758517761857388126507 13967637776642786082189761)
                ·
                  refine ⟨10475728332482089561642321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13967637776642786082189761 10475728332482089561642321)
                  ·
                    refine ⟨7856796249361567171231741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10475728332482089561642321 7856796249361567171231741)
                    ·
                      refine ⟨2946298593510587689211903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856796249361567171231741 2946298593510587689211903)
                      ·
                        rfl

theorem cell23_5737896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5737896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737896 prefixEnd_5737896 := by exact prefixLift 5737896
  have htrace : WordTrace (prefixWord ++ tailWord_5737896) baseStart_5737896 baseEnd_5737896 := by
    simpa [prefixWord, tailWord_5737896, baseEnd_5737896] using wordTrace_append hprefix tailTrace_5737896
  have hstable : (prefixWord ++ tailWord_5737896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737896).length < 2 ^ (prefixWord ++ tailWord_5737896).sum := by decide
  have hdescent : baseEnd_5737896 < baseStart_5737896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737932 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5737932 : Nat := 118140960795 + 5737932 * 2 ^ 59
def prefixEnd_5737932 : Nat := 4983230072969 + 3 ^ 40 * 5737932 * 2
def baseEnd_5737932 : Nat := 2946317078814149548361737

theorem tailTrace_5737932 : CollatzResearch.WordTrace tailWord_5737932 prefixEnd_5737932 2946317078814149548361737 := by
  unfold tailWord_5737932
  simp only [CollatzResearch.WordTrace]
  refine ⟨104639786524229899806024025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139519715365639866408032033 104639786524229899806024025)
  ·
    refine ⟨78479839893172424854518019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104639786524229899806024025 78479839893172424854518019)
    ·
      refine ⟨117719759839758637281777029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78479839893172424854518019 117719759839758637281777029)
      ·
        refine ⟨22072454969954744490333193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117719759839758637281777029 22072454969954744490333193)
        ·
          refine ⟨16554341227466058367749895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22072454969954744490333193 16554341227466058367749895)
          ·
            refine ⟨24831511841199087551624843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16554341227466058367749895 24831511841199087551624843)
            ·
              refine ⟨37247267761798631327437265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24831511841199087551624843 37247267761798631327437265)
              ·
                refine ⟨27935450821348973495577949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37247267761798631327437265 27935450821348973495577949)
                ·
                  refine ⟨10475794058005865060841731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27935450821348973495577949 10475794058005865060841731)
                  ·
                    refine ⟨15713691087008797591262597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10475794058005865060841731 15713691087008797591262597)
                    ·
                      refine ⟨2946317078814149548361737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15713691087008797591262597 2946317078814149548361737)
                      ·
                        rfl

theorem cell23_5737932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5737932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737932 prefixEnd_5737932 := by exact prefixLift 5737932
  have htrace : WordTrace (prefixWord ++ tailWord_5737932) baseStart_5737932 baseEnd_5737932 := by
    simpa [prefixWord, tailWord_5737932, baseEnd_5737932] using wordTrace_append hprefix tailTrace_5737932
  have hstable : (prefixWord ++ tailWord_5737932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737932).length < 2 ^ (prefixWord ++ tailWord_5737932).sum := by decide
  have hdescent : baseEnd_5737932 < baseStart_5737932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737935 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_5737935 : Nat := 118140960795 + 5737935 * 2 ^ 59
def prefixEnd_5737935 : Nat := 4983230072969 + 3 ^ 40 * 5737935 * 2
def baseEnd_5737935 : Nat := 2946318619256113036624223

theorem tailTrace_5737935 : CollatzResearch.WordTrace tailWord_5737935 prefixEnd_5737935 2946318619256113036624223 := by
  unfold tailWord_5737935
  simp only [CollatzResearch.WordTrace]
  refine ⟨209279682467448931124407259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139519788311632620749604839 209279682467448931124407259)
  ·
    refine ⟨313919523701173396686610889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209279682467448931124407259 313919523701173396686610889)
    ·
      refine ⟨235439642775880047514958167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313919523701173396686610889 235439642775880047514958167)
      ·
        refine ⟨353159464163820071272437251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235439642775880047514958167 353159464163820071272437251)
        ·
          refine ⟨529739196245730106908655877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353159464163820071272437251 529739196245730106908655877)
          ·
            refine ⟨99326099296074395045372977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 529739196245730106908655877 99326099296074395045372977)
            ·
              refine ⟨74494574472055796284029733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99326099296074395045372977 74494574472055796284029733)
              ·
                refine ⟨13967732713510461803255575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74494574472055796284029733 13967732713510461803255575)
                ·
                  refine ⟨20951599070265692704883363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13967732713510461803255575 20951599070265692704883363)
                  ·
                    refine ⟨31427398605398539057325045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20951599070265692704883363 31427398605398539057325045)
                    ·
                      refine ⟨2946318619256113036624223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31427398605398539057325045 2946318619256113036624223)
                      ·
                        rfl

theorem cell23_5737935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_5737935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737935 prefixEnd_5737935 := by exact prefixLift 5737935
  have htrace : WordTrace (prefixWord ++ tailWord_5737935) baseStart_5737935 baseEnd_5737935 := by
    simpa [prefixWord, tailWord_5737935, baseEnd_5737935] using wordTrace_append hprefix tailTrace_5737935
  have hstable : (prefixWord ++ tailWord_5737935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737935).length < 2 ^ (prefixWord ++ tailWord_5737935).sum := by decide
  have hdescent : baseEnd_5737935 < baseStart_5737935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737969 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_5737969 : Nat := 118140960795 + 5737969 * 2 ^ 59
def prefixEnd_5737969 : Nat := 4983230072969 + 3 ^ 40 * 5737969 * 2
def baseEnd_5737969 : Nat := 2946336077598365903599067

theorem tailTrace_5737969 : CollatzResearch.WordTrace tailWord_5737969 prefixEnd_5737969 2946336077598365903599067 := by
  unfold tailWord_5737969
  simp only [CollatzResearch.WordTrace]
  refine ⟨209280922549325754931144961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139520615032883836620763307 209280922549325754931144961)
  ·
    refine ⟨156960691911994316198358721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209280922549325754931144961 156960691911994316198358721)
    ·
      refine ⟨117720518933995737148769041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156960691911994316198358721 117720518933995737148769041)
      ·
        refine ⟨88290389200496802861576781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117720518933995737148769041 88290389200496802861576781)
        ·
          refine ⟨33108895950186301073091293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88290389200496802861576781 33108895950186301073091293)
          ·
            refine ⟨12415835981319862902409235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33108895950186301073091293 12415835981319862902409235)
            ·
              refine ⟨18623753971979794353613853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12415835981319862902409235 18623753971979794353613853)
              ·
                refine ⟨6983907739492422882605195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18623753971979794353613853 6983907739492422882605195)
                ·
                  refine ⟨10475861609238634323907793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6983907739492422882605195 10475861609238634323907793)
                  ·
                    refine ⟨7856896206928975742930845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10475861609238634323907793 7856896206928975742930845)
                    ·
                      refine ⟨2946336077598365903599067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856896206928975742930845 2946336077598365903599067)
                      ·
                        rfl

theorem cell23_5737969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_5737969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737969 prefixEnd_5737969 := by exact prefixLift 5737969
  have htrace : WordTrace (prefixWord ++ tailWord_5737969) baseStart_5737969 baseEnd_5737969 := by
    simpa [prefixWord, tailWord_5737969, baseEnd_5737969] using wordTrace_append hprefix tailTrace_5737969
  have hstable : (prefixWord ++ tailWord_5737969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737969).length < 2 ^ (prefixWord ++ tailWord_5737969).sum := by decide
  have hdescent : baseEnd_5737969 < baseStart_5737969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5737996 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 1, 2, 4]
def baseStart_5737996 : Nat := 118140960795 + 5737996 * 2 ^ 59
def prefixEnd_5737996 : Nat := 4983230072969 + 3 ^ 40 * 5737996 * 2
def baseEnd_5737996 : Nat := 2946349941576037297961443

theorem tailTrace_5737996 : CollatzResearch.WordTrace tailWord_5737996 prefixEnd_5737996 2946349941576037297961443 := by
  unfold tailWord_5737996
  simp only [CollatzResearch.WordTrace]
  refine ⟨104640953660113969271188921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139521271546818625694918561 104640953660113969271188921)
  ·
    refine ⟨78480715245085476953391691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104640953660113969271188921 78480715245085476953391691)
    ·
      refine ⟨117721072867628215430087537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78480715245085476953391691 117721072867628215430087537)
      ·
        refine ⟨88290804650721161572565653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117721072867628215430087537 88290804650721161572565653)
        ·
          refine ⟨4138631468002554448714015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88290804650721161572565653 4138631468002554448714015)
          ·
            refine ⟨6207947202003831673071023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4138631468002554448714015 6207947202003831673071023)
            ·
              refine ⟨9311920803005747509606535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6207947202003831673071023 9311920803005747509606535)
              ·
                refine ⟨13967881204508621264409803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9311920803005747509606535 13967881204508621264409803)
                ·
                  refine ⟨20951821806762931896614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13967881204508621264409803 20951821806762931896614705)
                  ·
                    refine ⟨15713866355072198922461029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20951821806762931896614705 15713866355072198922461029)
                    ·
                      refine ⟨2946349941576037297961443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15713866355072198922461029 2946349941576037297961443)
                      ·
                        rfl

theorem cell23_5737996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_5737996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5737996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5737996 prefixEnd_5737996 := by exact prefixLift 5737996
  have htrace : WordTrace (prefixWord ++ tailWord_5737996) baseStart_5737996 baseEnd_5737996 := by
    simpa [prefixWord, tailWord_5737996, baseEnd_5737996] using wordTrace_append hprefix tailTrace_5737996
  have hstable : (prefixWord ++ tailWord_5737996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5737996).length < 2 ^ (prefixWord ++ tailWord_5737996).sum := by decide
  have hdescent : baseEnd_5737996 < baseStart_5737996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5737996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738015 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 1, 8]
def baseStart_5738015 : Nat := 118140960795 + 5738015 * 2 ^ 59
def prefixEnd_5738015 : Nat := 4983230072969 + 3 ^ 40 * 5738015 * 2
def baseEnd_5738015 : Nat := 982119899236157574541285

theorem tailTrace_5738015 : CollatzResearch.WordTrace tailWord_5738015 prefixEnd_5738015 982119899236157574541285 := by
  unfold tailWord_5738015
  simp only [CollatzResearch.WordTrace]
  refine ⟨209282600307159104787319499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139521733538106069858212999 209282600307159104787319499)
  ·
    refine ⟨313923900460738657180979249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209282600307159104787319499 313923900460738657180979249)
    ·
      refine ⟨235442925345553992885734437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313923900460738657180979249 235442925345553992885734437)
      ·
        refine ⟨44145548502291373666075207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235442925345553992885734437 44145548502291373666075207)
        ·
          refine ⟨66218322753437060499112811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44145548502291373666075207 66218322753437060499112811)
          ·
            refine ⟨99327484130155590748669217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66218322753437060499112811 99327484130155590748669217)
            ·
              refine ⟨74495613097616693061501913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99327484130155590748669217 74495613097616693061501913)
              ·
                refine ⟨55871709823212519796126435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74495613097616693061501913 55871709823212519796126435)
                ·
                  refine ⟨83807564734818779694189653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55871709823212519796126435 83807564734818779694189653)
                  ·
                    refine ⟨982119899236157574541285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83807564734818779694189653 982119899236157574541285)
                    ·
                      rfl

theorem cell23_5738015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_5738015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738015 prefixEnd_5738015 := by exact prefixLift 5738015
  have htrace : WordTrace (prefixWord ++ tailWord_5738015) baseStart_5738015 baseEnd_5738015 := by
    simpa [prefixWord, tailWord_5738015, baseEnd_5738015] using wordTrace_append hprefix tailTrace_5738015
  have hstable : (prefixWord ++ tailWord_5738015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738015).length < 2 ^ (prefixWord ++ tailWord_5738015).sum := by decide
  have hdescent : baseEnd_5738015 < baseStart_5738015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738026 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_5738026 : Nat := 118140960795 + 5738026 * 2 ^ 59
def prefixEnd_5738026 : Nat := 4983230072969 + 3 ^ 40 * 5738026 * 2
def baseEnd_5738026 : Nat := 2946365345995672180586305

theorem tailTrace_5738026 : CollatzResearch.WordTrace tailWord_5738026 prefixEnd_5738026 2946365345995672180586305 := by
  unfold tailWord_5738026
  simp only [CollatzResearch.WordTrace]
  refine ⟨52320750377529813416492483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139522001006746169110646621 52320750377529813416492483)
  ·
    refine ⟨78481125566294720124738725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52320750377529813416492483 78481125566294720124738725)
    ·
      refine ⟨14715211043680260023388511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78481125566294720124738725 14715211043680260023388511)
      ·
        refine ⟨22072816565520390035082767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14715211043680260023388511 22072816565520390035082767)
        ·
          refine ⟨33109224848280585052624151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22072816565520390035082767 33109224848280585052624151)
          ·
            refine ⟨49663837272420877578936227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33109224848280585052624151 49663837272420877578936227)
            ·
              refine ⟨74495755908631316368404341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49663837272420877578936227 74495755908631316368404341)
              ·
                refine ⟨6983977116434185909537907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74495755908631316368404341 6983977116434185909537907)
                ·
                  refine ⟨10475965674651278864306861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6983977116434185909537907 10475965674651278864306861)
                  ·
                    refine ⟨3928487127994229574115073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10475965674651278864306861 3928487127994229574115073)
                    ·
                      refine ⟨2946365345995672180586305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3928487127994229574115073 2946365345995672180586305)
                      ·
                        rfl

theorem cell23_5738026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_5738026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738026 prefixEnd_5738026 := by exact prefixLift 5738026
  have htrace : WordTrace (prefixWord ++ tailWord_5738026) baseStart_5738026 baseEnd_5738026 := by
    simpa [prefixWord, tailWord_5738026, baseEnd_5738026] using wordTrace_append hprefix tailTrace_5738026
  have hstable : (prefixWord ++ tailWord_5738026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738026).length < 2 ^ (prefixWord ++ tailWord_5738026).sum := by decide
  have hdescent : baseEnd_5738026 < baseStart_5738026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738042 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_5738042 : Nat := 118140960795 + 5738042 * 2 ^ 59
def prefixEnd_5738042 : Nat := 4983230072969 + 3 ^ 40 * 5738042 * 2
def baseEnd_5738042 : Nat := 2946373561686144117986231

theorem tailTrace_5738042 : CollatzResearch.WordTrace tailWord_5738042 prefixEnd_5738042 2946373561686144117986231 := by
  unfold tailWord_5738042
  simp only [CollatzResearch.WordTrace]
  refine ⟨52320896269515322099638095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139522390052040858932368253 52320896269515322099638095)
  ·
    refine ⟨78481344404272983149457143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52320896269515322099638095 78481344404272983149457143)
    ·
      refine ⟨117722016606409474724185715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78481344404272983149457143 117722016606409474724185715)
      ·
        refine ⟨176583024909614212086278573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117722016606409474724185715 176583024909614212086278573)
        ·
          refine ⟨66218634341105329532354465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176583024909614212086278573 66218634341105329532354465)
          ·
            refine ⟨49663975755828997149265849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66218634341105329532354465 49663975755828997149265849)
            ·
              refine ⟨37247981816871747861949387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49663975755828997149265849 37247981816871747861949387)
              ·
                refine ⟨55871972725307621792924081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37247981816871747861949387 55871972725307621792924081)
                ·
                  refine ⟨41903979543980716344693061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55871972725307621792924081 41903979543980716344693061)
                  ·
                    refine ⟨7856996164496384314629949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41903979543980716344693061 7856996164496384314629949)
                    ·
                      refine ⟨2946373561686144117986231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7856996164496384314629949 2946373561686144117986231)
                      ·
                        rfl

theorem cell23_5738042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_5738042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738042 prefixEnd_5738042 := by exact prefixLift 5738042
  have htrace : WordTrace (prefixWord ++ tailWord_5738042) baseStart_5738042 baseEnd_5738042 := by
    simpa [prefixWord, tailWord_5738042, baseEnd_5738042] using wordTrace_append hprefix tailTrace_5738042
  have hstable : (prefixWord ++ tailWord_5738042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738042).length < 2 ^ (prefixWord ++ tailWord_5738042).sum := by decide
  have hdescent : baseEnd_5738042 < baseStart_5738042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738072 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_5738072 : Nat := 118140960795 + 5738072 * 2 ^ 59
def prefixEnd_5738072 : Nat := 4983230072969 + 3 ^ 40 * 5738072 * 2
def baseEnd_5738072 : Nat := 2946388966105779000611093

theorem tailTrace_5738072 : CollatzResearch.WordTrace tailWord_5738072 prefixEnd_5738072 2946388966105779000611093 := by
  unfold tailWord_5738072
  simp only [CollatzResearch.WordTrace]
  refine ⟨104642339633976301761072235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139523119511968402348096313 104642339633976301761072235)
  ·
    refine ⟨156963509450964452641608353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104642339633976301761072235 156963509450964452641608353)
    ·
      refine ⟨117722632088223339481206265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156963509450964452641608353 117722632088223339481206265)
      ·
        refine ⟨88291974066167504610904699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117722632088223339481206265 88291974066167504610904699)
        ·
          refine ⟨132437961099251256916357049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88291974066167504610904699 132437961099251256916357049)
          ·
            refine ⟨99328470824438442687267787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132437961099251256916357049 99328470824438442687267787)
            ·
              refine ⟨148992706236657664030901681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99328470824438442687267787 148992706236657664030901681)
              ·
                refine ⟨111744529677493248023176261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148992706236657664030901681 111744529677493248023176261)
                ·
                  refine ⟨20952099314529984004345549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111744529677493248023176261 20952099314529984004345549)
                  ·
                    refine ⟨7857037242948744001629581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20952099314529984004345549 7857037242948744001629581)
                    ·
                      refine ⟨2946388966105779000611093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7857037242948744001629581 2946388966105779000611093)
                      ·
                        rfl

theorem cell23_5738072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_5738072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738072 prefixEnd_5738072 := by exact prefixLift 5738072
  have htrace : WordTrace (prefixWord ++ tailWord_5738072) baseStart_5738072 baseEnd_5738072 := by
    simpa [prefixWord, tailWord_5738072, baseEnd_5738072] using wordTrace_append hprefix tailTrace_5738072
  have hstable : (prefixWord ++ tailWord_5738072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738072).length < 2 ^ (prefixWord ++ tailWord_5738072).sum := by decide
  have hdescent : baseEnd_5738072 < baseStart_5738072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738077 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5738077 : Nat := 118140960795 + 5738077 * 2 ^ 59
def prefixEnd_5738077 : Nat := 4983230072969 + 3 ^ 40 * 5738077 * 2
def baseEnd_5738077 : Nat := 2946391533509051481048571

theorem tailTrace_5738077 : CollatzResearch.WordTrace tailWord_5738077 prefixEnd_5738077 2946391533509051481048571 := by
  unfold tailWord_5738077
  simp only [CollatzResearch.WordTrace]
  refine ⟨209284861632934489376076485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139523241088622992917384323 209284861632934489376076485)
  ·
    refine ⟨39240911556175216758014341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209284861632934489376076485 39240911556175216758014341)
    ·
      refine ⟨7357670916782853142127689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39240911556175216758014341 7357670916782853142127689)
      ·
        refine ⟨5518253187587139856595767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7357670916782853142127689 5518253187587139856595767)
        ·
          refine ⟨8277379781380709784893651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5518253187587139856595767 8277379781380709784893651)
          ·
            refine ⟨12416069672071064677340477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8277379781380709784893651 12416069672071064677340477)
            ·
              refine ⟨4656026127026649254002679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12416069672071064677340477 4656026127026649254002679)
              ·
                refine ⟨6984039190539973881004019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656026127026649254002679 6984039190539973881004019)
                ·
                  refine ⟨10476058785809960821506029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6984039190539973881004019 10476058785809960821506029)
                  ·
                    refine ⟨3928522044678735308064761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10476058785809960821506029 3928522044678735308064761)
                    ·
                      refine ⟨2946391533509051481048571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3928522044678735308064761 2946391533509051481048571)
                      ·
                        rfl

theorem cell23_5738077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5738077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738077 prefixEnd_5738077 := by exact prefixLift 5738077
  have htrace : WordTrace (prefixWord ++ tailWord_5738077) baseStart_5738077 baseEnd_5738077 := by
    simpa [prefixWord, tailWord_5738077, baseEnd_5738077] using wordTrace_append hprefix tailTrace_5738077
  have hstable : (prefixWord ++ tailWord_5738077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738077).length < 2 ^ (prefixWord ++ tailWord_5738077).sum := by decide
  have hdescent : baseEnd_5738077 < baseStart_5738077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738096 : List Nat := [2, 1, 1, 1, 6, 1, 4, 2, 5]
def baseStart_5738096 : Nat := 118140960795 + 5738096 * 2 ^ 59
def prefixEnd_5738096 : Nat := 4983230072969 + 3 ^ 40 * 5738096 * 2
def baseEnd_5738096 : Nat := 327377921071276322967887

theorem tailTrace_5738096 : CollatzResearch.WordTrace tailWord_5738096 prefixEnd_5738096 327377921071276322967887 := by
  unfold tailWord_5738096
  simp only [CollatzResearch.WordTrace]
  refine ⟨104642777309932827810509071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139523703079910437080678761 104642777309932827810509071)
  ·
    refine ⟨156964165964899241715763607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104642777309932827810509071 156964165964899241715763607)
    ·
      refine ⟨235446248947348862573645411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156964165964899241715763607 235446248947348862573645411)
      ·
        refine ⟨353169373421023293860468117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235446248947348862573645411 353169373421023293860468117)
        ·
          refine ⟨16554814379110466899709443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 353169373421023293860468117 16554814379110466899709443)
          ·
            refine ⟨24832221568665700349564165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16554814379110466899709443 24832221568665700349564165)
            ·
              refine ⟨4656041544124818815543281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24832221568665700349564165 4656041544124818815543281)
              ·
                refine ⟨3492031158093614111657461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4656041544124818815543281 3492031158093614111657461)
                ·
                  refine ⟨327377921071276322967887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3492031158093614111657461 327377921071276322967887)
                  ·
                    rfl

theorem cell23_5738096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2, 5].length) (baseStart_5738096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738096 prefixEnd_5738096 := by exact prefixLift 5738096
  have htrace : WordTrace (prefixWord ++ tailWord_5738096) baseStart_5738096 baseEnd_5738096 := by
    simpa [prefixWord, tailWord_5738096, baseEnd_5738096] using wordTrace_append hprefix tailTrace_5738096
  have hstable : (prefixWord ++ tailWord_5738096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738096).length < 2 ^ (prefixWord ++ tailWord_5738096).sum := by decide
  have hdescent : baseEnd_5738096 < baseStart_5738096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738112 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4]
def baseStart_5738112 : Nat := 118140960795 + 5738112 * 2 ^ 59
def prefixEnd_5738112 : Nat := 4983230072969 + 3 ^ 40 * 5738112 * 2
def baseEnd_5738112 : Nat := 2946409505331958844110909

theorem tailTrace_5738112 : CollatzResearch.WordTrace tailWord_5738112 prefixEnd_5738112 2946409505331958844110909 := by
  unfold tailWord_5738112
  simp only [CollatzResearch.WordTrace]
  refine ⟨104643069093903845176800295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139524092125205126902400393 104643069093903845176800295)
  ·
    refine ⟨156964603640855767765200443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104643069093903845176800295 156964603640855767765200443)
    ·
      refine ⟨235446905461283651647800665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156964603640855767765200443 235446905461283651647800665)
      ·
        refine ⟨176585179095962738735850499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235446905461283651647800665 176585179095962738735850499)
        ·
          refine ⟨264877768643944108103775749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176585179095962738735850499 264877768643944108103775749)
          ·
            refine ⟨49664581620739520269457953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264877768643944108103775749 49664581620739520269457953)
            ·
              refine ⟨37248436215554640202093465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49664581620739520269457953 37248436215554640202093465)
              ·
                refine ⟨27936327161665980151570099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37248436215554640202093465 27936327161665980151570099)
                ·
                  refine ⟨41904490742498970227355149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27936327161665980151570099 41904490742498970227355149)
                  ·
                    refine ⟨15714184028437113835258181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41904490742498970227355149 15714184028437113835258181)
                    ·
                      refine ⟨2946409505331958844110909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15714184028437113835258181 2946409505331958844110909)
                      ·
                        rfl

theorem cell23_5738112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_5738112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738112 prefixEnd_5738112 := by exact prefixLift 5738112
  have htrace : WordTrace (prefixWord ++ tailWord_5738112) baseStart_5738112 baseEnd_5738112 := by
    simpa [prefixWord, tailWord_5738112, baseEnd_5738112] using wordTrace_append hprefix tailTrace_5738112
  have hstable : (prefixWord ++ tailWord_5738112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738112).length < 2 ^ (prefixWord ++ tailWord_5738112).sum := by decide
  have hdescent : baseEnd_5738112 < baseStart_5738112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738126 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_5738126 : Nat := 118140960795 + 5738126 * 2 ^ 59
def prefixEnd_5738126 : Nat := 4983230072969 + 3 ^ 40 * 5738126 * 2
def baseEnd_5738126 : Nat := 982138898020373929778615

theorem tailTrace_5738126 : CollatzResearch.WordTrace tailWord_5738126 prefixEnd_5738126 982138898020373929778615 := by
  unfold tailWord_5738126
  simp only [CollatzResearch.WordTrace]
  refine ⟨26160831101219621343076279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139524432539837980496406821 26160831101219621343076279)
  ·
    refine ⟨39241246651829432014614419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26160831101219621343076279 39241246651829432014614419)
    ·
      refine ⟨58861869977744148021921629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39241246651829432014614419 58861869977744148021921629)
      ·
        refine ⟨22073201241654055508220611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58861869977744148021921629 22073201241654055508220611)
        ·
          refine ⟨33109801862481083262330917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22073201241654055508220611 33109801862481083262330917)
          ·
            refine ⟨6208087849215203111687047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33109801862481083262330917 6208087849215203111687047)
            ·
              refine ⟨9312131773822804667530571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208087849215203111687047 9312131773822804667530571)
              ·
                refine ⟨13968197660734207001295857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9312131773822804667530571 13968197660734207001295857)
                ·
                  refine ⟨10476148245550655250971893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13968197660734207001295857 10476148245550655250971893)
                  ·
                    refine ⟨982138898020373929778615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10476148245550655250971893 982138898020373929778615)
                    ·
                      rfl

theorem cell23_5738126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_5738126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738126 prefixEnd_5738126 := by exact prefixLift 5738126
  have htrace : WordTrace (prefixWord ++ tailWord_5738126) baseStart_5738126 baseEnd_5738126 := by
    simpa [prefixWord, tailWord_5738126, baseEnd_5738126] using wordTrace_append hprefix tailTrace_5738126
  have hstable : (prefixWord ++ tailWord_5738126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738126).length < 2 ^ (prefixWord ++ tailWord_5738126).sum := by decide
  have hdescent : baseEnd_5738126 < baseStart_5738126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738149 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_5738149 : Nat := 118140960795 + 5738149 * 2 ^ 59
def prefixEnd_5738149 : Nat := 4983230072969 + 3 ^ 40 * 5738149 * 2
def baseEnd_5738149 : Nat := 2946428504116175199348239

theorem tailTrace_5738149 : CollatzResearch.WordTrace tailWord_5738149 prefixEnd_5738149 2946428504116175199348239 := by
  unfold tailWord_5738149
  simp only [CollatzResearch.WordTrace]
  refine ⟨209287487688673645672697501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139524991792449097115131667 209287487688673645672697501)
  ·
    refine ⟨78482807883252617127261563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209287487688673645672697501 78482807883252617127261563)
    ·
      refine ⟨117724211824878925690892345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78482807883252617127261563 117724211824878925690892345)
      ·
        refine ⟨88293158868659194268169259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117724211824878925690892345 88293158868659194268169259)
        ·
          refine ⟨132439738302988791402253889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88293158868659194268169259 132439738302988791402253889)
          ·
            refine ⟨99329803727241593551690417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132439738302988791402253889 99329803727241593551690417)
            ·
              refine ⟨74497352795431195163767813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99329803727241593551690417 74497352795431195163767813)
              ·
                refine ⟨13968253649143349093206465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74497352795431195163767813 13968253649143349093206465)
                ·
                  refine ⟨10476190236857511819904849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13968253649143349093206465 10476190236857511819904849)
                  ·
                    refine ⟨7857142677643133864928637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10476190236857511819904849 7857142677643133864928637)
                    ·
                      refine ⟨2946428504116175199348239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7857142677643133864928637 2946428504116175199348239)
                      ·
                        rfl

theorem cell23_5738149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_5738149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738149 prefixEnd_5738149 := by exact prefixLift 5738149
  have htrace : WordTrace (prefixWord ++ tailWord_5738149) baseStart_5738149 baseEnd_5738149 := by
    simpa [prefixWord, tailWord_5738149, baseEnd_5738149] using wordTrace_append hprefix tailTrace_5738149
  have hstable : (prefixWord ++ tailWord_5738149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738149).length < 2 ^ (prefixWord ++ tailWord_5738149).sum := by decide
  have hdescent : baseEnd_5738149 < baseStart_5738149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738199 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 1, 5]
def baseStart_5738199 : Nat := 118140960795 + 5738199 * 2 ^ 59
def prefixEnd_5738199 : Nat := 4983230072969 + 3 ^ 40 * 5738199 * 2
def baseEnd_5738199 : Nat := 982151392716300001241003

theorem tailTrace_5738199 : CollatzResearch.WordTrace tailWord_5738199 prefixEnd_5738199 982151392716300001241003 := by
  unfold tailWord_5738199
  simp only [CollatzResearch.WordTrace]
  refine ⟨209289311338492504212017651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139526207558995002808011767 209289311338492504212017651)
  ·
    refine ⟨313933967007738756318026477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209289311338492504212017651 313933967007738756318026477)
    ·
      refine ⟨117725237627902033619259929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313933967007738756318026477 117725237627902033619259929)
      ·
        refine ⟨88293928220926525214444947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117725237627902033619259929 88293928220926525214444947)
        ·
          refine ⟨132440892331389787821667421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88293928220926525214444947 132440892331389787821667421)
          ·
            refine ⟨49665334624271170433125283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132440892331389787821667421 49665334624271170433125283)
            ·
              refine ⟨74498001936406755649687925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49665334624271170433125283 74498001936406755649687925)
              ·
                refine ⟨6984187681538133342158243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74498001936406755649687925 6984187681538133342158243)
                ·
                  refine ⟨10476281522307200013237365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6984187681538133342158243 10476281522307200013237365)
                  ·
                    refine ⟨982151392716300001241003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10476281522307200013237365 982151392716300001241003)
                    ·
                      rfl

theorem cell23_5738199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_5738199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738199 prefixEnd_5738199 := by exact prefixLift 5738199
  have htrace : WordTrace (prefixWord ++ tailWord_5738199) baseStart_5738199 baseEnd_5738199 := by
    simpa [prefixWord, tailWord_5738199, baseEnd_5738199] using wordTrace_append hprefix tailTrace_5738199
  have hstable : (prefixWord ++ tailWord_5738199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738199).length < 2 ^ (prefixWord ++ tailWord_5738199).sum := by decide
  have hdescent : baseEnd_5738199 < baseStart_5738199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738263 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 2, 4]
def baseStart_5738263 : Nat := 118140960795 + 5738263 * 2 ^ 59
def prefixEnd_5738263 : Nat := 4983230072969 + 3 ^ 40 * 5738263 * 2
def baseEnd_5738263 : Nat := 982162346970262584440905

theorem tailTrace_5738263 : CollatzResearch.WordTrace tailWord_5738263 prefixEnd_5738263 982162346970262584440905 := by
  unfold tailWord_5738263
  simp only [CollatzResearch.WordTrace]
  refine ⟨209291645610260643142347443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139527763740173762094898295 209291645610260643142347443)
  ·
    refine ⟨313937468415390964713521165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209291645610260643142347443 313937468415390964713521165)
    ·
      refine ⟨117726550655771611767570437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313937468415390964713521165 117726550655771611767570437)
      ·
        refine ⟨22073728247957177206419457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117726550655771611767570437 22073728247957177206419457)
        ·
          refine ⟨16555296185967882904814593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22073728247957177206419457 16555296185967882904814593)
          ·
            refine ⟨12416472139475912178610945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16555296185967882904814593 12416472139475912178610945)
            ·
              refine ⟨9312354104606934133958209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12416472139475912178610945 9312354104606934133958209)
              ·
                refine ⟨6984265578455200600468657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9312354104606934133958209 6984265578455200600468657)
                ·
                  refine ⟨5238199183841400450351493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6984265578455200600468657 5238199183841400450351493)
                  ·
                    refine ⟨982162346970262584440905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238199183841400450351493 982162346970262584440905)
                    ·
                      rfl

theorem cell23_5738263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_5738263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738263 prefixEnd_5738263 := by exact prefixLift 5738263
  have htrace : WordTrace (prefixWord ++ tailWord_5738263) baseStart_5738263 baseEnd_5738263 := by
    simpa [prefixWord, tailWord_5738263, baseEnd_5738263] using wordTrace_append hprefix tailTrace_5738263
  have hstable : (prefixWord ++ tailWord_5738263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738263).length < 2 ^ (prefixWord ++ tailWord_5738263).sum := by decide
  have hdescent : baseEnd_5738263 < baseStart_5738263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738276 : List Nat := [2, 3, 1, 3, 2, 3, 1, 8]
def baseStart_5738276 : Nat := 118140960795 + 5738276 * 2 ^ 59
def prefixEnd_5738276 : Nat := 4983230072969 + 3 ^ 40 * 5738276 * 2
def baseEnd_5738276 : Nat := 109129396894788748239265

theorem tailTrace_5738276 : CollatzResearch.WordTrace tailWord_5738276 prefixEnd_5738276 109129396894788748239265 := by
  unfold tailWord_5738276
  simp only [CollatzResearch.WordTrace]
  refine ⟨104646059879606773181285341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139528079839475697575047121 104646059879606773181285341)
  ·
    refine ⟨39242272454852539942982003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104646059879606773181285341 39242272454852539942982003)
    ·
      refine ⟨58863408682278809914473005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39242272454852539942982003 58863408682278809914473005)
      ·
        refine ⟨22073778255854553717927377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58863408682278809914473005 22073778255854553717927377)
        ·
          refine ⟨16555333691890915288445533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22073778255854553717927377 16555333691890915288445533)
          ·
            refine ⟨6208250134459093233167075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16555333691890915288445533 6208250134459093233167075)
            ·
              refine ⟨9312375201688639849750613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208250134459093233167075 9312375201688639849750613)
              ·
                refine ⟨109129396894788748239265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9312375201688639849750613 109129396894788748239265)
                ·
                  rfl

theorem cell23_5738276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 8].length) (baseStart_5738276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738276 prefixEnd_5738276 := by exact prefixLift 5738276
  have htrace : WordTrace (prefixWord ++ tailWord_5738276) baseStart_5738276 baseEnd_5738276 := by
    simpa [prefixWord, tailWord_5738276, baseEnd_5738276] using wordTrace_append hprefix tailTrace_5738276
  have hstable : (prefixWord ++ tailWord_5738276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738276).length < 2 ^ (prefixWord ++ tailWord_5738276).sum := by decide
  have hdescent : baseEnd_5738276 < baseStart_5738276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738313 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 1, 3, 2]
def baseStart_5738313 : Nat := 118140960795 + 5738313 * 2 ^ 59
def prefixEnd_5738313 : Nat := 4983230072969 + 3 ^ 40 * 5738313 * 2
def baseEnd_5738313 : Nat := 2946512714943512557697485

theorem tailTrace_5738313 : CollatzResearch.WordTrace tailWord_5738313 prefixEnd_5738313 2946512714943512557697485 := by
  unfold tailWord_5738313
  simp only [CollatzResearch.WordTrace]
  refine ⟨209293469260079501681667593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139528979506719667787778395 209293469260079501681667593)
  ·
    refine ⟨156970101945059626261250695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209293469260079501681667593 156970101945059626261250695)
    ·
      refine ⟨235455152917589439391876043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156970101945059626261250695 235455152917589439391876043)
      ·
        refine ⟨353182729376384159087814065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235455152917589439391876043 353182729376384159087814065)
        ·
          refine ⟨264887047032288119315860549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353182729376384159087814065 264887047032288119315860549)
          ·
            refine ⟨49666321318554022371723853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264887047032288119315860549 49666321318554022371723853)
            ·
              refine ⟨18624870494457758389396445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49666321318554022371723853 18624870494457758389396445)
              ·
                refine ⟨6984326435421659396023667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18624870494457758389396445 6984326435421659396023667)
                ·
                  refine ⟨10476489653132489094035501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6984326435421659396023667 10476489653132489094035501)
                  ·
                    refine ⟨3928683619924683410263313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10476489653132489094035501 3928683619924683410263313)
                    ·
                      refine ⟨2946512714943512557697485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3928683619924683410263313 2946512714943512557697485)
                      ·
                        rfl

theorem cell23_5738313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 3, 2].length) (baseStart_5738313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738313 prefixEnd_5738313 := by exact prefixLift 5738313
  have htrace : WordTrace (prefixWord ++ tailWord_5738313) baseStart_5738313 baseEnd_5738313 := by
    simpa [prefixWord, tailWord_5738313, baseEnd_5738313] using wordTrace_append hprefix tailTrace_5738313
  have hstable : (prefixWord ++ tailWord_5738313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738313).length < 2 ^ (prefixWord ++ tailWord_5738313).sum := by decide
  have hdescent : baseEnd_5738313 < baseStart_5738313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738394 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2]
def baseStart_5738394 : Nat := 118140960795 + 5738394 * 2 ^ 59
def prefixEnd_5738394 : Nat := 4983230072969 + 3 ^ 40 * 5738394 * 2
def baseEnd_5738394 : Nat := 2946554306876526740784613

theorem tailTrace_5738394 : CollatzResearch.WordTrace tailWord_5738394 prefixEnd_5738394 2946554306876526740784613 := by
  unfold tailWord_5738394
  simp only [CollatzResearch.WordTrace]
  refine ⟨52324105893196513128841559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139530949048524035010244157 52324105893196513128841559)
  ·
    refine ⟨78486158839794769693262339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52324105893196513128841559 78486158839794769693262339)
    ·
      refine ⟨117729238259692154539893509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78486158839794769693262339 117729238259692154539893509)
      ·
        refine ⟨22074232173692278976230033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117729238259692154539893509 22074232173692278976230033)
        ·
          refine ⟨16555674130269209232172525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22074232173692278976230033 16555674130269209232172525)
          ·
            refine ⟨6208377798850953462064697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16555674130269209232172525 6208377798850953462064697)
            ·
              refine ⟨4656283349138215096548523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6208377798850953462064697 4656283349138215096548523)
              ·
                refine ⟨6984425023707322644822785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656283349138215096548523 6984425023707322644822785)
                ·
                  refine ⟨5238318767780491983617089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6984425023707322644822785 5238318767780491983617089)
                  ·
                    refine ⟨3928739075835368987712817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5238318767780491983617089 3928739075835368987712817)
                    ·
                      refine ⟨2946554306876526740784613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3928739075835368987712817 2946554306876526740784613)
                      ·
                        rfl

theorem cell23_5738394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_5738394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738394 prefixEnd_5738394 := by exact prefixLift 5738394
  have htrace : WordTrace (prefixWord ++ tailWord_5738394) baseStart_5738394 baseEnd_5738394 := by
    simpa [prefixWord, tailWord_5738394, baseEnd_5738394] using wordTrace_append hprefix tailTrace_5738394
  have hstable : (prefixWord ++ tailWord_5738394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738394).length < 2 ^ (prefixWord ++ tailWord_5738394).sum := by decide
  have hdescent : baseEnd_5738394 < baseStart_5738394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738426 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_5738426 : Nat := 118140960795 + 5738426 * 2 ^ 59
def prefixEnd_5738426 : Nat := 4983230072969 + 3 ^ 40 * 5738426 * 2
def baseEnd_5738426 : Nat := 982190246085823538528155

theorem tailTrace_5738426 : CollatzResearch.WordTrace tailWord_5738426 prefixEnd_5738426 982190246085823538528155 := by
  unfold tailWord_5738426
  simp only [CollatzResearch.WordTrace]
  refine ⟨52324397677167530495132783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139531727139113414653687421 52324397677167530495132783)
  ·
    refine ⟨78486596515751295742699175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52324397677167530495132783 78486596515751295742699175)
    ·
      refine ⟨117729894773626943614048763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78486596515751295742699175 117729894773626943614048763)
      ·
        refine ⟨176594842160440415421073145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117729894773626943614048763 176594842160440415421073145)
        ·
          refine ⟨132446131620330311565804859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176594842160440415421073145 132446131620330311565804859)
          ·
            refine ⟨198669197430495467348707289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132446131620330311565804859 198669197430495467348707289)
            ·
              refine ⟨149001898072871600511530467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198669197430495467348707289 149001898072871600511530467)
              ·
                refine ⟨223502847109307400767295701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149001898072871600511530467 223502847109307400767295701)
                ·
                  refine ⟨5238347979124392205483493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 223502847109307400767295701 5238347979124392205483493)
                  ·
                    refine ⟨982190246085823538528155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238347979124392205483493 982190246085823538528155)
                    ·
                      rfl

theorem cell23_5738426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_5738426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738426 prefixEnd_5738426 := by exact prefixLift 5738426
  have htrace : WordTrace (prefixWord ++ tailWord_5738426) baseStart_5738426 baseEnd_5738426 := by
    simpa [prefixWord, tailWord_5738426, baseEnd_5738426] using wordTrace_append hprefix tailTrace_5738426
  have hstable : (prefixWord ++ tailWord_5738426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738426).length < 2 ^ (prefixWord ++ tailWord_5738426).sum := by decide
  have hdescent : baseEnd_5738426 < baseStart_5738426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738456 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 6]
def baseStart_5738456 : Nat := 118140960795 + 5738456 * 2 ^ 59
def prefixEnd_5738456 : Nat := 4983230072969 + 3 ^ 40 * 5738456 * 2
def baseEnd_5738456 : Nat := 327398460297456166467703

theorem tailTrace_5738456 : CollatzResearch.WordTrace tailWord_5738456 prefixEnd_5738456 327398460297456166467703 := by
  unfold tailWord_5738456
  simp only [CollatzResearch.WordTrace]
  refine ⟨104649342449280718552061611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139532456599040958069415481 104649342449280718552061611)
  ·
    refine ⟨156974013673921077828092417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104649342449280718552061611 156974013673921077828092417)
    ·
      refine ⟨117730510255440808371069313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156974013673921077828092417 117730510255440808371069313)
      ·
        refine ⟨88297882691580606278301985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117730510255440808371069313 88297882691580606278301985)
        ·
          refine ⟨66223412018685454708726489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88297882691580606278301985 66223412018685454708726489)
          ·
            refine ⟨49667559014014091031544867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66223412018685454708726489 49667559014014091031544867)
            ·
              refine ⟨74501338521021136547317301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49667559014014091031544867 74501338521021136547317301)
              ·
                refine ⟨6984500486345731551310997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74501338521021136547317301 6984500486345731551310997)
                ·
                  refine ⟨327398460297456166467703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6984500486345731551310997 327398460297456166467703)
                  ·
                    rfl

theorem cell23_5738456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 6].length) (baseStart_5738456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738456 prefixEnd_5738456 := by exact prefixLift 5738456
  have htrace : WordTrace (prefixWord ++ tailWord_5738456) baseStart_5738456 baseEnd_5738456 := by
    simpa [prefixWord, tailWord_5738456, baseEnd_5738456] using wordTrace_append hprefix tailTrace_5738456
  have hstable : (prefixWord ++ tailWord_5738456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738456).length < 2 ^ (prefixWord ++ tailWord_5738456).sum := by decide
  have hdescent : baseEnd_5738456 < baseStart_5738456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738533 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_5738533 : Nat := 118140960795 + 5738533 * 2 ^ 59
def prefixEnd_5738533 : Nat := 4983230072969 + 3 ^ 40 * 5738533 * 2
def baseEnd_5738533 : Nat := 982208560229167232315491

theorem tailTrace_5738533 : CollatzResearch.WordTrace tailWord_5738533 prefixEnd_5738533 982208560229167232315491 := by
  unfold tailWord_5738533
  simp only [CollatzResearch.WordTrace]
  refine ⟨209301493319282479254676253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139534328879521652836450835 209301493319282479254676253)
  ·
    refine ⟨78488059994730929720503595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209301493319282479254676253 78488059994730929720503595)
    ·
      refine ⟨117732089992096394580755393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78488059994730929720503595 117732089992096394580755393)
      ·
        refine ⟨88299067494072295935566545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117732089992096394580755393 88299067494072295935566545)
        ·
          refine ⟨66224300620554221951674909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88299067494072295935566545 66224300620554221951674909)
          ·
            refine ⟨24834112732707833231878091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66224300620554221951674909 24834112732707833231878091)
            ·
              refine ⟨37251169099061749847817137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24834112732707833231878091 37251169099061749847817137)
              ·
                refine ⟨27938376824296312385862853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37251169099061749847817137 27938376824296312385862853)
                ·
                  refine ⟨5238445654555558572349285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27938376824296312385862853 5238445654555558572349285)
                  ·
                    refine ⟨982208560229167232315491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238445654555558572349285 982208560229167232315491)
                    ·
                      rfl

theorem cell23_5738533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_5738533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738533 prefixEnd_5738533 := by exact prefixLift 5738533
  have htrace : WordTrace (prefixWord ++ tailWord_5738533) baseStart_5738533 baseEnd_5738533 := by
    simpa [prefixWord, tailWord_5738533, baseEnd_5738533] using wordTrace_append hprefix tailTrace_5738533
  have hstable : (prefixWord ++ tailWord_5738533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738533).length < 2 ^ (prefixWord ++ tailWord_5738533).sum := by decide
  have hdescent : baseEnd_5738533 < baseStart_5738533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738546 : List Nat := [3, 2, 1, 1, 2, 3, 11]
def baseStart_5738546 : Nat := 118140960795 + 5738546 * 2 ^ 59
def prefixEnd_5738546 : Nat := 4983230072969 + 3 ^ 40 * 5738546 * 2
def baseEnd_5738546 : Nat := 36378177233777903038073

theorem tailTrace_5738546 : CollatzResearch.WordTrace tailWord_5738546 prefixEnd_5738546 36378177233777903038073 := by
  unfold tailWord_5738546
  simp only [CollatzResearch.WordTrace]
  refine ⟨52325491867058845618724873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139534644978823588316599661 52325491867058845618724873)
  ·
    refine ⟨39244118900294134214043655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52325491867058845618724873 39244118900294134214043655)
    ·
      refine ⟨58866178350441201321065483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39244118900294134214043655 58866178350441201321065483)
      ·
        refine ⟨88299267525661801981598225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58866178350441201321065483 88299267525661801981598225)
        ·
          refine ⟨66224450644246351486198669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88299267525661801981598225 66224450644246351486198669)
          ·
            refine ⟨24834168991592381807324501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66224450644246351486198669 24834168991592381807324501)
            ·
              refine ⟨36378177233777903038073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24834168991592381807324501 36378177233777903038073)
              ·
                rfl

theorem cell23_5738546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 11].length) (baseStart_5738546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738546 prefixEnd_5738546 := by exact prefixLift 5738546
  have htrace : WordTrace (prefixWord ++ tailWord_5738546) baseStart_5738546 baseEnd_5738546 := by
    simpa [prefixWord, tailWord_5738546, baseEnd_5738546] using wordTrace_append hprefix tailTrace_5738546
  have hstable : (prefixWord ++ tailWord_5738546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738546).length < 2 ^ (prefixWord ++ tailWord_5738546).sum := by decide
  have hdescent : baseEnd_5738546 < baseStart_5738546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738550 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_5738550 : Nat := 118140960795 + 5738550 * 2 ^ 59
def prefixEnd_5738550 : Nat := 4983230072969 + 3 ^ 40 * 5738550 * 2
def baseEnd_5738550 : Nat := 982211469952876043477965

theorem tailTrace_5738550 : CollatzResearch.WordTrace tailWord_5738550 prefixEnd_5738550 982211469952876043477965 := by
  unfold tailWord_5738550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13081382085013805697377819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139534742240147260772030069 13081382085013805697377819)
  ·
    refine ⟨19622073127520708546066729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13081382085013805697377819 19622073127520708546066729)
    ·
      refine ⟨14716554845640531409550047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19622073127520708546066729 14716554845640531409550047)
      ·
        refine ⟨22074832268460797114325071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14716554845640531409550047 22074832268460797114325071)
        ·
          refine ⟨33112248402691195671487607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22074832268460797114325071 33112248402691195671487607)
          ·
            refine ⟨49668372604036793507231411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33112248402691195671487607 49668372604036793507231411)
            ·
              refine ⟨74502558906055190260847117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49668372604036793507231411 74502558906055190260847117)
              ·
                refine ⟨27938459589770696347817669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74502558906055190260847117 27938459589770696347817669)
                ·
                  refine ⟨5238461173082005565215813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27938459589770696347817669 5238461173082005565215813)
                  ·
                    refine ⟨982211469952876043477965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238461173082005565215813 982211469952876043477965)
                    ·
                      rfl

theorem cell23_5738550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_5738550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738550 prefixEnd_5738550 := by exact prefixLift 5738550
  have htrace : WordTrace (prefixWord ++ tailWord_5738550) baseStart_5738550 baseEnd_5738550 := by
    simpa [prefixWord, tailWord_5738550, baseEnd_5738550] using wordTrace_append hprefix tailTrace_5738550
  have hstable : (prefixWord ++ tailWord_5738550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738550).length < 2 ^ (prefixWord ++ tailWord_5738550).sum := by decide
  have hdescent : baseEnd_5738550 < baseStart_5738550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738594 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5738594 : Nat := 118140960795 + 5738594 * 2 ^ 59
def prefixEnd_5738594 : Nat := 4983230072969 + 3 ^ 40 * 5738594 * 2
def baseEnd_5738594 : Nat := 2946657003007425958283693

theorem tailTrace_5738594 : CollatzResearch.WordTrace tailWord_5738594 prefixEnd_5738594 2946657003007425958283693 := by
  unfold tailWord_5738594
  simp only [CollatzResearch.WordTrace]
  refine ⟨52325929543015371668161709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139535812114707657781764557 52325929543015371668161709)
  ·
    refine ⟨19622223578630764375560641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52325929543015371668161709 19622223578630764375560641)
    ·
      refine ⟨14716667683973073281670481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19622223578630764375560641 14716667683973073281670481)
      ·
        refine ⟨11037500762979804961252861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14716667683973073281670481 11037500762979804961252861)
        ·
          refine ⟨4139062786117426860469823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11037500762979804961252861 4139062786117426860469823)
          ·
            refine ⟨6208594179176140290704735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139062786117426860469823 6208594179176140290704735)
            ·
              refine ⟨9312891268764210436057103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208594179176140290704735 9312891268764210436057103)
              ·
                refine ⟨13969336903146315654085655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9312891268764210436057103 13969336903146315654085655)
                ·
                  refine ⟨20954005354719473481128483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13969336903146315654085655 20954005354719473481128483)
                  ·
                    refine ⟨31431008032079210221692725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20954005354719473481128483 31431008032079210221692725)
                    ·
                      refine ⟨2946657003007425958283693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31431008032079210221692725 2946657003007425958283693)
                      ·
                        rfl

theorem cell23_5738594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5738594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738594 prefixEnd_5738594 := by exact prefixLift 5738594
  have htrace : WordTrace (prefixWord ++ tailWord_5738594) baseStart_5738594 baseEnd_5738594 := by
    simpa [prefixWord, tailWord_5738594, baseEnd_5738594] using wordTrace_append hprefix tailTrace_5738594
  have hstable : (prefixWord ++ tailWord_5738594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738594).length < 2 ^ (prefixWord ++ tailWord_5738594).sum := by decide
  have hdescent : baseEnd_5738594 < baseStart_5738594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738607 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 3]
def baseStart_5738607 : Nat := 118140960795 + 5738607 * 2 ^ 59
def prefixEnd_5738607 : Nat := 4983230072969 + 3 ^ 40 * 5738607 * 2
def baseEnd_5738607 : Nat := 2946663678255934407421133

theorem tailTrace_5738607 : CollatzResearch.WordTrace tailWord_5738607 prefixEnd_5738607 2946663678255934407421133 := by
  unfold tailWord_5738607
  simp only [CollatzResearch.WordTrace]
  refine ⟨209304192321014389892870075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139536128214009593261913383 209304192321014389892870075)
  ·
    refine ⟨313956288481521584839305113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209304192321014389892870075 313956288481521584839305113)
    ·
      refine ⟨235467216361141188629478835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313956288481521584839305113 235467216361141188629478835)
      ·
        refine ⟨353200824541711782944218253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235467216361141188629478835 353200824541711782944218253)
        ·
          refine ⟨132450309203141918604081845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353200824541711782944218253 132450309203141918604081845)
          ·
            refine ⟨12417216487794554869132673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132450309203141918604081845 12417216487794554869132673)
            ·
              refine ⟨9312912365845916151849505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12417216487794554869132673 9312912365845916151849505)
              ·
                refine ⟨6984684274384437113887129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9312912365845916151849505 6984684274384437113887129)
                ·
                  refine ⟨5238513205788327835415347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6984684274384437113887129 5238513205788327835415347)
                  ·
                    refine ⟨7857769808682491753123021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5238513205788327835415347 7857769808682491753123021)
                    ·
                      refine ⟨2946663678255934407421133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7857769808682491753123021 2946663678255934407421133)
                      ·
                        rfl

theorem cell23_5738607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 1, 3].length) (baseStart_5738607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738607 prefixEnd_5738607 := by exact prefixLift 5738607
  have htrace : WordTrace (prefixWord ++ tailWord_5738607) baseStart_5738607 baseEnd_5738607 := by
    simpa [prefixWord, tailWord_5738607, baseEnd_5738607] using wordTrace_append hprefix tailTrace_5738607
  have hstable : (prefixWord ++ tailWord_5738607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738607).length < 2 ^ (prefixWord ++ tailWord_5738607).sum := by decide
  have hdescent : baseEnd_5738607 < baseStart_5738607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738633 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 3]
def baseStart_5738633 : Nat := 118140960795 + 5738633 * 2 ^ 59
def prefixEnd_5738633 : Nat := 4983230072969 + 3 ^ 40 * 5738633 * 2
def baseEnd_5738633 : Nat := 2946677028752951305696013

theorem tailTrace_5738633 : CollatzResearch.WordTrace tailWord_5738633 prefixEnd_5738633 2946677028752951305696013 := by
  unfold tailWord_5738633
  simp only [CollatzResearch.WordTrace]
  refine ⟨209305140618920196333316553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139536760412613464222211035 209305140618920196333316553)
  ·
    refine ⟨156978855464190147249987415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209305140618920196333316553 156978855464190147249987415)
    ·
      refine ⟨235468283196285220874981123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156978855464190147249987415 235468283196285220874981123)
      ·
        refine ⟨353202424794427831312471685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235468283196285220874981123 353202424794427831312471685)
        ·
          refine ⟨66225454648955218371088441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353202424794427831312471685 66225454648955218371088441)
          ·
            refine ⟨49669090986716413778316331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66225454648955218371088441 49669090986716413778316331)
            ·
              refine ⟨74503636480074620667474497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49669090986716413778316331 74503636480074620667474497)
              ·
                refine ⟨55877727360055965500605873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74503636480074620667474497 55877727360055965500605873)
                ·
                  refine ⟨41908295520041974125454405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55877727360055965500605873 41908295520041974125454405)
                  ·
                    refine ⟨7857805410007870148522701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41908295520041974125454405 7857805410007870148522701)
                    ·
                      refine ⟨2946677028752951305696013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7857805410007870148522701 2946677028752951305696013)
                      ·
                        rfl

theorem cell23_5738633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_5738633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738633 prefixEnd_5738633 := by exact prefixLift 5738633
  have htrace : WordTrace (prefixWord ++ tailWord_5738633) baseStart_5738633 baseEnd_5738633 := by
    simpa [prefixWord, tailWord_5738633, baseEnd_5738633] using wordTrace_append hprefix tailTrace_5738633
  have hstable : (prefixWord ++ tailWord_5738633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738633).length < 2 ^ (prefixWord ++ tailWord_5738633).sum := by decide
  have hdescent : baseEnd_5738633 < baseStart_5738633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738703 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_5738703 : Nat := 118140960795 + 5738703 * 2 ^ 59
def prefixEnd_5738703 : Nat := 4983230072969 + 3 ^ 40 * 5738703 * 2
def baseEnd_5738703 : Nat := 2946712972398766031820691

theorem tailTrace_5738703 : CollatzResearch.WordTrace tailWord_5738703 prefixEnd_5738703 2946712972398766031820691 := by
  unfold tailWord_5738703
  simp only [CollatzResearch.WordTrace]
  refine ⟨209307693728666598288364763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139538462485777732192243175 209307693728666598288364763)
  ·
    refine ⟨313961540592999897432547145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209307693728666598288364763 313961540592999897432547145)
    ·
      refine ⟨235471155444749923074410359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313961540592999897432547145 235471155444749923074410359)
      ·
        refine ⟨353206733167124884611615539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235471155444749923074410359 353206733167124884611615539)
        ·
          refine ⟨529810099750687326917423309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353206733167124884611615539 529810099750687326917423309)
          ·
            refine ⟨198678787406507747594033741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 529810099750687326917423309 198678787406507747594033741)
            ·
              refine ⟨74504545277440405347762653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198678787406507747594033741 74504545277440405347762653)
              ·
                refine ⟨27939204479040152005410995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74504545277440405347762653 27939204479040152005410995)
                ·
                  refine ⟨41908806718560228008116493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27939204479040152005410995 41908806718560228008116493)
                  ·
                    refine ⟨15715802519460085503043685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41908806718560228008116493 15715802519460085503043685)
                    ·
                      refine ⟨2946712972398766031820691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15715802519460085503043685 2946712972398766031820691)
                      ·
                        rfl

theorem cell23_5738703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_5738703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738703 prefixEnd_5738703 := by exact prefixLift 5738703
  have htrace : WordTrace (prefixWord ++ tailWord_5738703) baseStart_5738703 baseEnd_5738703 := by
    simpa [prefixWord, tailWord_5738703, baseEnd_5738703] using wordTrace_append hprefix tailTrace_5738703
  have hstable : (prefixWord ++ tailWord_5738703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738703).length < 2 ^ (prefixWord ++ tailWord_5738703).sum := by decide
  have hdescent : baseEnd_5738703 < baseStart_5738703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738717 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_5738717 : Nat := 118140960795 + 5738717 * 2 ^ 59
def prefixEnd_5738717 : Nat := 4983230072969 + 3 ^ 40 * 5738717 * 2
def baseEnd_5738717 : Nat := 982240053709309659015209

theorem tailTrace_5738717 : CollatzResearch.WordTrace tailWord_5738717 prefixEnd_5738717 982240053709309659015209 := by
  unfold tailWord_5738717
  simp only [CollatzResearch.WordTrace]
  refine ⟨209308204350615878679374405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139538802900410585786249603 209308204350615878679374405)
  ·
    refine ⟨39245288315740477252382701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209308204350615878679374405 39245288315740477252382701)
    ·
      refine ⟨14716983118402678969643513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39245288315740477252382701 14716983118402678969643513)
      ·
        refine ⟨11037737338802009227232635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14716983118402678969643513 11037737338802009227232635)
        ·
          refine ⟨16556606008203013840848953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11037737338802009227232635 16556606008203013840848953)
          ·
            refine ⟨12417454506152260380636715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16556606008203013840848953 12417454506152260380636715)
            ·
              refine ⟨18626181759228390570955073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12417454506152260380636715 18626181759228390570955073)
              ·
                refine ⟨13969636319421292928216305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18626181759228390570955073 13969636319421292928216305)
                ·
                  refine ⟨10477227239565969696162229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13969636319421292928216305 10477227239565969696162229)
                  ·
                    refine ⟨982240053709309659015209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10477227239565969696162229 982240053709309659015209)
                    ·
                      rfl

theorem cell23_5738717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_5738717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738717 prefixEnd_5738717 := by exact prefixLift 5738717
  have htrace : WordTrace (prefixWord ++ tailWord_5738717) baseStart_5738717 baseEnd_5738717 := by
    simpa [prefixWord, tailWord_5738717, baseEnd_5738717] using wordTrace_append hprefix tailTrace_5738717
  have hstable : (prefixWord ++ tailWord_5738717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738717).length < 2 ^ (prefixWord ++ tailWord_5738717).sum := by decide
  have hdescent : baseEnd_5738717 < baseStart_5738717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738720 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4]
def baseStart_5738720 : Nat := 118140960795 + 5738720 * 2 ^ 59
def prefixEnd_5738720 : Nat := 4983230072969 + 3 ^ 40 * 5738720 * 2
def baseEnd_5738720 : Nat := 2946721701569892465308113

theorem tailTrace_5738720 : CollatzResearch.WordTrace tailWord_5738720 prefixEnd_5738720 2946721701569892465308113 := by
  unfold tailWord_5738720
  simp only [CollatzResearch.WordTrace]
  refine ⟨104654156884802505095866807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139538875846403340127822409 104654156884802505095866807)
  ·
    refine ⟨156981235327203757643800211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104654156884802505095866807 156981235327203757643800211)
    ·
      refine ⟨235471852990805636465700317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156981235327203757643800211 235471852990805636465700317)
      ·
        refine ⟨88301944871552113674637619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235471852990805636465700317 88301944871552113674637619)
        ·
          refine ⟨132452917307328170511956429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88301944871552113674637619 132452917307328170511956429)
          ·
            refine ⟨49669843990248063941983661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132452917307328170511956429 49669843990248063941983661)
            ·
              refine ⟨18626191496343023978243873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49669843990248063941983661 18626191496343023978243873)
              ·
                refine ⟨13969643622257267983682905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18626191496343023978243873 13969643622257267983682905)
                ·
                  refine ⟨10477232716692950987762179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13969643622257267983682905 10477232716692950987762179)
                  ·
                    refine ⟨15715849075039426481643269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10477232716692950987762179 15715849075039426481643269)
                    ·
                      refine ⟨2946721701569892465308113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15715849075039426481643269 2946721701569892465308113)
                      ·
                        rfl

theorem cell23_5738720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_5738720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738720 prefixEnd_5738720 := by exact prefixLift 5738720
  have htrace : WordTrace (prefixWord ++ tailWord_5738720) baseStart_5738720 baseEnd_5738720 := by
    simpa [prefixWord, tailWord_5738720, baseEnd_5738720] using wordTrace_append hprefix tailTrace_5738720
  have hstable : (prefixWord ++ tailWord_5738720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738720).length < 2 ^ (prefixWord ++ tailWord_5738720).sum := by decide
  have hdescent : baseEnd_5738720 < baseStart_5738720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738754 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_5738754 : Nat := 118140960795 + 5738754 * 2 ^ 59
def prefixEnd_5738754 : Nat := 4983230072969 + 3 ^ 40 * 5738754 * 2
def baseEnd_5738754 : Nat := 2946739159912145332282957

theorem tailTrace_5738754 : CollatzResearch.WordTrace tailWord_5738754 prefixEnd_5738754 2946739159912145332282957 := by
  unfold tailWord_5738754
  simp only [CollatzResearch.WordTrace]
  refine ⟨52327388462870458499617829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139539702567654555998980877 52327388462870458499617829)
  ·
    refine ⟨9811385336788210968678343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52327388462870458499617829 9811385336788210968678343)
    ·
      refine ⟨14717078005182316453017515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811385336788210968678343 14717078005182316453017515)
      ·
        refine ⟨22075617007773474679526273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14717078005182316453017515 22075617007773474679526273)
        ·
          refine ⟨16556712755830106009644705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22075617007773474679526273 16556712755830106009644705)
          ·
            refine ⟨12417534566872579507233529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16556712755830106009644705 12417534566872579507233529)
            ·
              refine ⟨9313150925154434630425147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12417534566872579507233529 9313150925154434630425147)
              ·
                refine ⟨13969726387731651945637721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9313150925154434630425147 13969726387731651945637721)
                ·
                  refine ⟨10477294790798738959228291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13969726387731651945637721 10477294790798738959228291)
                  ·
                    refine ⟨15715942186198108438842437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10477294790798738959228291 15715942186198108438842437)
                    ·
                      refine ⟨2946739159912145332282957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15715942186198108438842437 2946739159912145332282957)
                      ·
                        rfl

theorem cell23_5738754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_5738754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738754 prefixEnd_5738754 := by exact prefixLift 5738754
  have htrace : WordTrace (prefixWord ++ tailWord_5738754) baseStart_5738754 baseEnd_5738754 := by
    simpa [prefixWord, tailWord_5738754, baseEnd_5738754] using wordTrace_append hprefix tailTrace_5738754
  have hstable : (prefixWord ++ tailWord_5738754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738754).length < 2 ^ (prefixWord ++ tailWord_5738754).sum := by decide
  have hdescent : baseEnd_5738754 < baseStart_5738754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738781 : List Nat := [1, 4, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_5738781 : Nat := 118140960795 + 5738781 * 2 ^ 59
def prefixEnd_5738781 : Nat := 4983230072969 + 3 ^ 40 * 5738781 * 2
def baseEnd_5738781 : Nat := 982251007963272242215111

theorem tailTrace_5738781 : CollatzResearch.WordTrace tailWord_5738781 prefixEnd_5738781 982251007963272242215111 := by
  unfold tailWord_5738781
  simp only [CollatzResearch.WordTrace]
  refine ⟨209310538622384017609704197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139540359081589345073136131 209310538622384017609704197)
  ·
    refine ⟨39245725991697003301819537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209310538622384017609704197 39245725991697003301819537)
    ·
      refine ⟨29434294493772752476364653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39245725991697003301819537 29434294493772752476364653)
      ·
        refine ⟨11037860435164782178636745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29434294493772752476364653 11037860435164782178636745)
        ·
          refine ⟨8278395326373586633977559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11037860435164782178636745 8278395326373586633977559)
          ·
            refine ⟨12417592989560379950966339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278395326373586633977559 12417592989560379950966339)
            ·
              refine ⟨18626389484340569926449509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12417592989560379950966339 18626389484340569926449509)
              ·
                refine ⟨3492448028313856861209283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18626389484340569926449509 3492448028313856861209283)
                ·
                  refine ⟨5238672042470785291813925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492448028313856861209283 5238672042470785291813925)
                  ·
                    refine ⟨982251007963272242215111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238672042470785291813925 982251007963272242215111)
                    ·
                      rfl

theorem cell23_5738781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_5738781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738781 prefixEnd_5738781 := by exact prefixLift 5738781
  have htrace : WordTrace (prefixWord ++ tailWord_5738781) baseStart_5738781 baseEnd_5738781 := by
    simpa [prefixWord, tailWord_5738781, baseEnd_5738781] using wordTrace_append hprefix tailTrace_5738781
  have hstable : (prefixWord ++ tailWord_5738781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738781).length < 2 ^ (prefixWord ++ tailWord_5738781).sum := by decide
  have hdescent : baseEnd_5738781 < baseStart_5738781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738787 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 3]
def baseStart_5738787 : Nat := 118140960795 + 5738787 * 2 ^ 59
def prefixEnd_5738787 : Nat := 4983230072969 + 3 ^ 40 * 5738787 * 2
def baseEnd_5738787 : Nat := 2946756104773743703170305

theorem tailTrace_5738787 : CollatzResearch.WordTrace tailWord_5738787 prefixEnd_5738787 2946756104773743703170305 := by
  unfold tailWord_5738787
  simp only [CollatzResearch.WordTrace]
  refine ⟨209310757460362280634422615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139540504973574853756281743 209310757460362280634422615)
  ·
    refine ⟨313966136190543420951633923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209310757460362280634422615 313966136190543420951633923)
    ·
      refine ⟨470949204285815131427450885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313966136190543420951633923 470949204285815131427450885)
      ·
        refine ⟨88302975803590337142647041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 470949204285815131427450885 88302975803590337142647041)
        ·
          refine ⟨66227231852692752856985281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88302975803590337142647041 66227231852692752856985281)
          ·
            refine ⟨49670423889519564642738961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66227231852692752856985281 49670423889519564642738961)
            ·
              refine ⟨37252817917139673482054221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49670423889519564642738961 37252817917139673482054221)
              ·
                refine ⟨13969806718927377555770333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37252817917139673482054221 13969806718927377555770333)
                ·
                  refine ⟨5238677519597766583413875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13969806718927377555770333 5238677519597766583413875)
                  ·
                    refine ⟨7858016279396649875120813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5238677519597766583413875 7858016279396649875120813)
                    ·
                      refine ⟨2946756104773743703170305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858016279396649875120813 2946756104773743703170305)
                      ·
                        rfl

theorem cell23_5738787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_5738787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738787 prefixEnd_5738787 := by exact prefixLift 5738787
  have htrace : WordTrace (prefixWord ++ tailWord_5738787) baseStart_5738787 baseEnd_5738787 := by
    simpa [prefixWord, tailWord_5738787, baseEnd_5738787] using wordTrace_append hprefix tailTrace_5738787
  have hstable : (prefixWord ++ tailWord_5738787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738787).length < 2 ^ (prefixWord ++ tailWord_5738787).sum := by decide
  have hdescent : baseEnd_5738787 < baseStart_5738787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738804 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_5738804 : Nat := 118140960795 + 5738804 * 2 ^ 59
def prefixEnd_5738804 : Nat := 4983230072969 + 3 ^ 40 * 5738804 * 2
def baseEnd_5738804 : Nat := 2946764833944870136657727

theorem tailTrace_5738804 : CollatzResearch.WordTrace tailWord_5738804 prefixEnd_5738804 2946764833944870136657727 := by
  unfold tailWord_5738804
  simp only [CollatzResearch.WordTrace]
  refine ⟨104655688750650346268895733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139540918334200461691860977 104655688750650346268895733)
  ·
    refine ⟨9811470820373469962708975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104655688750650346268895733 9811470820373469962708975)
    ·
      refine ⟨14717206230560204944063463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811470820373469962708975 14717206230560204944063463)
      ·
        refine ⟨22075809345840307416095195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14717206230560204944063463 22075809345840307416095195)
        ·
          refine ⟨33113714018760461124142793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22075809345840307416095195 33113714018760461124142793)
          ·
            refine ⟨24835285514070345843107095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33113714018760461124142793 24835285514070345843107095)
            ·
              refine ⟨37252928271105518764660643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24835285514070345843107095 37252928271105518764660643)
              ·
                refine ⟨55879392406658278146990965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37252928271105518764660643 55879392406658278146990965)
                ·
                  refine ⟨5238693038124213576280403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55879392406658278146990965 5238693038124213576280403)
                  ·
                    refine ⟨7858039557186320364420605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5238693038124213576280403 7858039557186320364420605)
                    ·
                      refine ⟨2946764833944870136657727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858039557186320364420605 2946764833944870136657727)
                      ·
                        rfl

theorem cell23_5738804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_5738804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738804 prefixEnd_5738804 := by exact prefixLift 5738804
  have htrace : WordTrace (prefixWord ++ tailWord_5738804) baseStart_5738804 baseEnd_5738804 := by
    simpa [prefixWord, tailWord_5738804, baseEnd_5738804] using wordTrace_append hprefix tailTrace_5738804
  have hstable : (prefixWord ++ tailWord_5738804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738804).length < 2 ^ (prefixWord ++ tailWord_5738804).sum := by decide
  have hdescent : baseEnd_5738804 < baseStart_5738804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738814 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_5738814 : Nat := 118140960795 + 5738814 * 2 ^ 59
def prefixEnd_5738814 : Nat := 4983230072969 + 3 ^ 40 * 5738814 * 2
def baseEnd_5738814 : Nat := 2946769968751415097532681

theorem tailTrace_5738814 : CollatzResearch.WordTrace tailWord_5738814 prefixEnd_5738814 2946769968751415097532681 := by
  unfold tailWord_5738814
  simp only [CollatzResearch.WordTrace]
  refine ⟨26163967778908058030706937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139541161487509642830436997 26163967778908058030706937)
  ·
    refine ⟨19622975834181043523030203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26163967778908058030706937 19622975834181043523030203)
    ·
      refine ⟨29434463751271565284545305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19622975834181043523030203 29434463751271565284545305)
      ·
        refine ⟨22075847813453673963408979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29434463751271565284545305 22075847813453673963408979)
        ·
          refine ⟨33113771720180510945113469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22075847813453673963408979 33113771720180510945113469)
          ·
            refine ⟨12417664395067691604417551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33113771720180510945113469 12417664395067691604417551)
            ·
              refine ⟨18626496592601537406626327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12417664395067691604417551 18626496592601537406626327)
              ·
                refine ⟨27939744888902306109939491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18626496592601537406626327 27939744888902306109939491)
                ·
                  refine ⟨41909617333353459164909237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27939744888902306109939491 41909617333353459164909237)
                  ·
                    refine ⟨3929026625001886796710241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41909617333353459164909237 3929026625001886796710241)
                    ·
                      refine ⟨2946769968751415097532681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929026625001886796710241 2946769968751415097532681)
                      ·
                        rfl

theorem cell23_5738814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_5738814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738814 prefixEnd_5738814 := by exact prefixLift 5738814
  have htrace : WordTrace (prefixWord ++ tailWord_5738814) baseStart_5738814 baseEnd_5738814 := by
    simpa [prefixWord, tailWord_5738814, baseEnd_5738814] using wordTrace_append hprefix tailTrace_5738814
  have hstable : (prefixWord ++ tailWord_5738814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738814).length < 2 ^ (prefixWord ++ tailWord_5738814).sum := by decide
  have hdescent : baseEnd_5738814 < baseStart_5738814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738864 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3]
def baseStart_5738864 : Nat := 118140960795 + 5738864 * 2 ^ 59
def prefixEnd_5738864 : Nat := 4983230072969 + 3 ^ 40 * 5738864 * 2
def baseEnd_5738864 : Nat := 2946795642784139901907451

theorem tailTrace_5738864 : CollatzResearch.WordTrace tailWord_5738864 prefixEnd_5738864 2946795642784139901907451 := by
  unfold tailWord_5738864
  simp only [CollatzResearch.WordTrace]
  refine ⟨104656782940541661392487823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139542377254055548523317097 104656782940541661392487823)
  ·
    refine ⟨156985174410812492088731735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104656782940541661392487823 156985174410812492088731735)
    ·
      refine ⟨235477761616218738133097603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156985174410812492088731735 235477761616218738133097603)
      ·
        refine ⟨353216642424328107199646405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235477761616218738133097603 353216642424328107199646405)
        ·
          refine ⟨66228120454561520099933701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353216642424328107199646405 66228120454561520099933701)
          ·
            refine ⟨12417772585230285018737569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66228120454561520099933701 12417772585230285018737569)
            ·
              refine ⟨9313329438922713764053177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12417772585230285018737569 9313329438922713764053177)
              ·
                refine ⟨6984997079192035323039883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9313329438922713764053177 6984997079192035323039883)
                ·
                  refine ⟨10477495618788052984559825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6984997079192035323039883 10477495618788052984559825)
                  ·
                    refine ⟨7858121714091039738419869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10477495618788052984559825 7858121714091039738419869)
                    ·
                      refine ⟨2946795642784139901907451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858121714091039738419869 2946795642784139901907451)
                      ·
                        rfl

theorem cell23_5738864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 3].length) (baseStart_5738864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738864 prefixEnd_5738864 := by exact prefixLift 5738864
  have htrace : WordTrace (prefixWord ++ tailWord_5738864) baseStart_5738864 baseEnd_5738864 := by
    simpa [prefixWord, tailWord_5738864, baseEnd_5738864] using wordTrace_append hprefix tailTrace_5738864
  have hstable : (prefixWord ++ tailWord_5738864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738864).length < 2 ^ (prefixWord ++ tailWord_5738864).sum := by decide
  have hdescent : baseEnd_5738864 < baseStart_5738864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738937 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5738937 : Nat := 118140960795 + 5738937 * 2 ^ 59
def prefixEnd_5738937 : Nat := 4983230072969 + 3 ^ 40 * 5738937 * 2
def baseEnd_5738937 : Nat := 2946833126871918116294615

theorem tailTrace_5738937 : CollatzResearch.WordTrace tailWord_5738937 prefixEnd_5738937 2946833126871918116294615 := by
  unfold tailWord_5738937
  simp only [CollatzResearch.WordTrace]
  refine ⟨209316228409818856252383065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139544152273212570834922043 209316228409818856252383065)
  ·
    refine ⟨156987171307364142189287299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209316228409818856252383065 156987171307364142189287299)
    ·
      refine ⟨235480756961046213283930949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156987171307364142189287299 235480756961046213283930949)
      ·
        refine ⟨44152641930196164990737053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235480756961046213283930949 44152641930196164990737053)
        ·
          refine ⟨16557240723823561871526395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44152641930196164990737053 16557240723823561871526395)
          ·
            refine ⟨24835861085735342807289593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16557240723823561871526395 24835861085735342807289593)
            ·
              refine ⟨18626895814301507105467195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24835861085735342807289593 18626895814301507105467195)
              ·
                refine ⟨27940343721452260658200793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18626895814301507105467195 27940343721452260658200793)
                ·
                  refine ⟨20955257791089195493650595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27940343721452260658200793 20955257791089195493650595)
                  ·
                    refine ⟨31432886686633793240475893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20955257791089195493650595 31432886686633793240475893)
                    ·
                      refine ⟨2946833126871918116294615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31432886686633793240475893 2946833126871918116294615)
                      ·
                        rfl

theorem cell23_5738937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5738937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738937 prefixEnd_5738937 := by exact prefixLift 5738937
  have htrace : WordTrace (prefixWord ++ tailWord_5738937) baseStart_5738937 baseEnd_5738937 := by
    simpa [prefixWord, tailWord_5738937, baseEnd_5738937] using wordTrace_append hprefix tailTrace_5738937
  have hstable : (prefixWord ++ tailWord_5738937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738937).length < 2 ^ (prefixWord ++ tailWord_5738937).sum := by decide
  have hdescent : baseEnd_5738937 < baseStart_5738937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738951 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_5738951 : Nat := 118140960795 + 5738951 * 2 ^ 59
def prefixEnd_5738951 : Nat := 4983230072969 + 3 ^ 40 * 5738951 * 2
def baseEnd_5738951 : Nat := 2946840315601081061519551

theorem tailTrace_5738951 : CollatzResearch.WordTrace tailWord_5738951 prefixEnd_5738951 2946840315601081061519551 := by
  unfold tailWord_5738951
  simp only [CollatzResearch.WordTrace]
  refine ⟨209316739031768136643392707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139544492687845424428928471 209316739031768136643392707)
  ·
    refine ⟨313975108547652204965089061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209316739031768136643392707 313975108547652204965089061)
    ·
      refine ⟨58870332852684788430954199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313975108547652204965089061 58870332852684788430954199)
      ·
        refine ⟨88305499279027182646431299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58870332852684788430954199 88305499279027182646431299)
        ·
          refine ⟨132458248918540773969646949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88305499279027182646431299 132458248918540773969646949)
          ·
            refine ⟨24835921672226395119308803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132458248918540773969646949 24835921672226395119308803)
            ·
              refine ⟨37253882508339592678963205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24835921672226395119308803 37253882508339592678963205)
              ·
                refine ⟨6985102970313673627305601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37253882508339592678963205 6985102970313673627305601)
                ·
                  refine ⟨5238827227735255220479201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6985102970313673627305601 5238827227735255220479201)
                  ·
                    refine ⟨3929120420801441415359401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5238827227735255220479201 3929120420801441415359401)
                    ·
                      refine ⟨2946840315601081061519551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929120420801441415359401 2946840315601081061519551)
                      ·
                        rfl

theorem cell23_5738951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_5738951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738951 prefixEnd_5738951 := by exact prefixLift 5738951
  have htrace : WordTrace (prefixWord ++ tailWord_5738951) baseStart_5738951 baseEnd_5738951 := by
    simpa [prefixWord, tailWord_5738951, baseEnd_5738951] using wordTrace_append hprefix tailTrace_5738951
  have hstable : (prefixWord ++ tailWord_5738951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738951).length < 2 ^ (prefixWord ++ tailWord_5738951).sum := by decide
  have hdescent : baseEnd_5738951 < baseStart_5738951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5738964 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5738964 : Nat := 118140960795 + 5738964 * 2 ^ 59
def prefixEnd_5738964 : Nat := 4983230072969 + 3 ^ 40 * 5738964 * 2
def baseEnd_5738964 : Nat := 2946846990849589510656991

theorem tailTrace_5738964 : CollatzResearch.WordTrace tailWord_5738964 prefixEnd_5738964 2946846990849589510656991 := by
  unfold tailWord_5738964
  simp only [CollatzResearch.WordTrace]
  refine ⟨104658606590360519931807973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139544808787147359909077297 104658606590360519931807973)
  ·
    refine ⟨19623488735692597487213995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104658606590360519931807973 19623488735692597487213995)
    ·
      refine ⟨29435233103538896230820993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19623488735692597487213995 29435233103538896230820993)
      ·
        refine ⟨22076424827654172173115745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29435233103538896230820993 22076424827654172173115745)
        ·
          refine ⟨16557318620740629129836809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22076424827654172173115745 16557318620740629129836809)
          ·
            refine ⟨12417988965555471847377607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16557318620740629129836809 12417988965555471847377607)
            ·
              refine ⟨18626983448333207771066411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12417988965555471847377607 18626983448333207771066411)
              ·
                refine ⟨27940475172499811656599617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18626983448333207771066411 27940475172499811656599617)
                ·
                  refine ⟨20955356379374858742449713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27940475172499811656599617 20955356379374858742449713)
                  ·
                    refine ⟨15716517284531144056837285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20955356379374858742449713 15716517284531144056837285)
                    ·
                      refine ⟨2946846990849589510656991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15716517284531144056837285 2946846990849589510656991)
                      ·
                        rfl

theorem cell23_5738964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5738964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5738964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5738964 prefixEnd_5738964 := by exact prefixLift 5738964
  have htrace : WordTrace (prefixWord ++ tailWord_5738964) baseStart_5738964 baseEnd_5738964 := by
    simpa [prefixWord, tailWord_5738964, baseEnd_5738964] using wordTrace_append hprefix tailTrace_5738964
  have hstable : (prefixWord ++ tailWord_5738964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5738964).length < 2 ^ (prefixWord ++ tailWord_5738964).sum := by decide
  have hdescent : baseEnd_5738964 < baseStart_5738964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5738964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739007 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_5739007 : Nat := 118140960795 + 5739007 * 2 ^ 59
def prefixEnd_5739007 : Nat := 4983230072969 + 3 ^ 40 * 5739007 * 2
def baseEnd_5739007 : Nat := 2946869070517732842419293

theorem tailTrace_5739007 : CollatzResearch.WordTrace tailWord_5739007 prefixEnd_5739007 2946869070517732842419293 := by
  unfold tailWord_5739007
  simp only [CollatzResearch.WordTrace]
  refine ⟨209318781519565258207431275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139545854346376838804954183 209318781519565258207431275)
  ·
    refine ⟨313978172279347887311146913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209318781519565258207431275 313978172279347887311146913)
    ·
      refine ⟨235483629209510915483360185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313978172279347887311146913 235483629209510915483360185)
      ·
        refine ⟨176612721907133186612520139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235483629209510915483360185 176612721907133186612520139)
        ·
          refine ⟨264919082860699779918780209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176612721907133186612520139 264919082860699779918780209)
          ·
            refine ⟨198689312145524834939085157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264919082860699779918780209 198689312145524834939085157)
            ·
              refine ⟨37254246027285906551078467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198689312145524834939085157 37254246027285906551078467)
              ·
                refine ⟨55881369040928859826617701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37254246027285906551078467 55881369040928859826617701)
                ·
                  refine ⟨10477756695174161217490819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55881369040928859826617701 10477756695174161217490819)
                  ·
                    refine ⟨15716635042761241826236229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10477756695174161217490819 15716635042761241826236229)
                    ·
                      refine ⟨2946869070517732842419293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15716635042761241826236229 2946869070517732842419293)
                      ·
                        rfl

theorem cell23_5739007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_5739007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739007 prefixEnd_5739007 := by exact prefixLift 5739007
  have htrace : WordTrace (prefixWord ++ tailWord_5739007) baseStart_5739007 baseEnd_5739007 := by
    simpa [prefixWord, tailWord_5739007, baseEnd_5739007] using wordTrace_append hprefix tailTrace_5739007
  have hstable : (prefixWord ++ tailWord_5739007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739007).length < 2 ^ (prefixWord ++ tailWord_5739007).sum := by decide
  have hdescent : baseEnd_5739007 < baseStart_5739007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739021 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_5739021 : Nat := 118140960795 + 5739021 * 2 ^ 59
def prefixEnd_5739021 : Nat := 4983230072969 + 3 ^ 40 * 5739021 * 2
def baseEnd_5739021 : Nat := 982292086415631929214743

theorem tailTrace_5739021 : CollatzResearch.WordTrace tailWord_5739021 prefixEnd_5739021 982292086415631929214743 := by
  unfold tailWord_5739021
  simp only [CollatzResearch.WordTrace]
  refine ⟨209319292141514538598440917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139546194761009692398960611 209319292141514538598440917)
  ·
    refine ⟨4905920909566746998400959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 209319292141514538598440917 4905920909566746998400959)
    ·
      refine ⟨7358881364350120497601439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4905920909566746998400959 7358881364350120497601439)
      ·
        refine ⟨11038322046525180746402159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7358881364350120497601439 11038322046525180746402159)
        ·
          refine ⟨16557483069787771119603239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11038322046525180746402159 16557483069787771119603239)
          ·
            refine ⟨24836224604681656679404859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16557483069787771119603239 24836224604681656679404859)
            ·
              refine ⟨37254336907022485019107289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24836224604681656679404859 37254336907022485019107289)
              ·
                refine ⟨27940752680266863764330467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37254336907022485019107289 27940752680266863764330467)
                ·
                  refine ⟨41911129020400295646495701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27940752680266863764330467 41911129020400295646495701)
                  ·
                    refine ⟨982292086415631929214743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41911129020400295646495701 982292086415631929214743)
                    ·
                      rfl

theorem cell23_5739021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_5739021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739021 prefixEnd_5739021 := by exact prefixLift 5739021
  have htrace : WordTrace (prefixWord ++ tailWord_5739021) baseStart_5739021 baseEnd_5739021 := by
    simpa [prefixWord, tailWord_5739021, baseEnd_5739021] using wordTrace_append hprefix tailTrace_5739021
  have hstable : (prefixWord ++ tailWord_5739021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739021).length < 2 ^ (prefixWord ++ tailWord_5739021).sum := by decide
  have hdescent : baseEnd_5739021 < baseStart_5739021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739027 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 3]
def baseStart_5739027 : Nat := 118140960795 + 5739027 * 2 ^ 59
def prefixEnd_5739027 : Nat := 4983230072969 + 3 ^ 40 * 5739027 * 2
def baseEnd_5739027 : Nat := 2946879340130822764169201

theorem tailTrace_5739027 : CollatzResearch.WordTrace tailWord_5739027 prefixEnd_5739027 2946879340130822764169201 := by
  unfold tailWord_5739027
  simp only [CollatzResearch.WordTrace]
  refine ⟨209319510979492801623159335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139546340652995201082106223 209319510979492801623159335)
  ·
    refine ⟨313979266469239202434739003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209319510979492801623159335 313979266469239202434739003)
    ·
      refine ⟨470968899703858803652108505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313979266469239202434739003 470968899703858803652108505)
      ·
        refine ⟨353226674777894102739081379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470968899703858803652108505 353226674777894102739081379)
        ·
          refine ⟨529840012166841154108622069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353226674777894102739081379 529840012166841154108622069)
          ·
            refine ⟨49672501140641358197683319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 529840012166841154108622069 49672501140641358197683319)
            ·
              refine ⟨74508751710962037296524979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49672501140641358197683319 74508751710962037296524979)
              ·
                refine ⟨111763127566443055944787469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74508751710962037296524979 111763127566443055944787469)
                ·
                  refine ⟨41911172837416145979295301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111763127566443055944787469 41911172837416145979295301)
                  ·
                    refine ⟨7858344907015527371117869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41911172837416145979295301 7858344907015527371117869)
                    ·
                      refine ⟨2946879340130822764169201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858344907015527371117869 2946879340130822764169201)
                      ·
                        rfl

theorem cell23_5739027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_5739027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739027 prefixEnd_5739027 := by exact prefixLift 5739027
  have htrace : WordTrace (prefixWord ++ tailWord_5739027) baseStart_5739027 baseEnd_5739027 := by
    simpa [prefixWord, tailWord_5739027, baseEnd_5739027] using wordTrace_append hprefix tailTrace_5739027
  have hstable : (prefixWord ++ tailWord_5739027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739027).length < 2 ^ (prefixWord ++ tailWord_5739027).sum := by decide
  have hdescent : baseEnd_5739027 < baseStart_5739027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739034 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_5739034 : Nat := 118140960795 + 5739034 * 2 ^ 59
def prefixEnd_5739034 : Nat := 4983230072969 + 3 ^ 40 * 5739034 * 2
def baseEnd_5739034 : Nat := 982294311498468078927223

theorem tailTrace_5739034 : CollatzResearch.WordTrace tailWord_5739034 prefixEnd_5739034 982294311498468078927223 := by
  unfold tailWord_5739034
  simp only [CollatzResearch.WordTrace]
  refine ⟨52329941572616860454666039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139546510860311627879109437 52329941572616860454666039)
  ·
    refine ⟨78494912358925290681999059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52329941572616860454666039 78494912358925290681999059)
    ·
      refine ⟨117742368538387936022998589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78494912358925290681999059 117742368538387936022998589)
      ·
        refine ⟨44153388201895476008624471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117742368538387936022998589 44153388201895476008624471)
        ·
          refine ⟨66230082302843214012936707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44153388201895476008624471 66230082302843214012936707)
          ·
            refine ⟨99345123454264821019405061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66230082302843214012936707 99345123454264821019405061)
            ·
              refine ⟨18627210647674653941138449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99345123454264821019405061 18627210647674653941138449)
              ·
                refine ⟨13970407985755990455853837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18627210647674653941138449 13970407985755990455853837)
                ·
                  refine ⟨5238902994658496420945189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13970407985755990455853837 5238902994658496420945189)
                  ·
                    refine ⟨982294311498468078927223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5238902994658496420945189 982294311498468078927223)
                    ·
                      rfl

theorem cell23_5739034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_5739034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739034 prefixEnd_5739034 := by exact prefixLift 5739034
  have htrace : WordTrace (prefixWord ++ tailWord_5739034) baseStart_5739034 baseEnd_5739034 := by
    simpa [prefixWord, tailWord_5739034, baseEnd_5739034] using wordTrace_append hprefix tailTrace_5739034
  have hstable : (prefixWord ++ tailWord_5739034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739034).length < 2 ^ (prefixWord ++ tailWord_5739034).sum := by decide
  have hdescent : baseEnd_5739034 < baseStart_5739034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739108 : List Nat := [2, 3, 1, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_5739108 : Nat := 118140960795 + 5739108 * 2 ^ 59
def prefixEnd_5739108 : Nat := 4983230072969 + 3 ^ 40 * 5739108 * 2
def baseEnd_5739108 : Nat := 2946920932063836947256329

theorem tailTrace_5739108 : CollatzResearch.WordTrace tailWord_5739108 prefixEnd_5739108 2946920932063836947256329 := by
  unfold tailWord_5739108
  simp only [CollatzResearch.WordTrace]
  refine ⟨104661232646099676228428989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139548310194799568304571985 104661232646099676228428989)
  ·
    refine ⟨39247962242287378585660871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104661232646099676228428989 39247962242287378585660871)
    ·
      refine ⟨58871943363431067878491307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39247962242287378585660871 58871943363431067878491307)
      ·
        refine ⟨88307915045146601817736961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58871943363431067878491307 88307915045146601817736961)
        ·
          refine ⟨66230936283859951363302721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88307915045146601817736961 66230936283859951363302721)
          ·
            refine ⟨49673202212894963522477041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66230936283859951363302721 49673202212894963522477041)
            ·
              refine ⟨37254901659671222641857781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49673202212894963522477041 37254901659671222641857781)
              ·
                refine ⟨3492647030594177122674167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37254901659671222641857781 3492647030594177122674167)
                ·
                  refine ⟨5238970545891265684011251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492647030594177122674167 5238970545891265684011251)
                  ·
                    refine ⟨7858455818836898526016877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5238970545891265684011251 7858455818836898526016877)
                    ·
                      refine ⟨2946920932063836947256329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858455818836898526016877 2946920932063836947256329)
                      ·
                        rfl

theorem cell23_5739108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_5739108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739108 prefixEnd_5739108 := by exact prefixLift 5739108
  have htrace : WordTrace (prefixWord ++ tailWord_5739108) baseStart_5739108 baseEnd_5739108 := by
    simpa [prefixWord, tailWord_5739108, baseEnd_5739108] using wordTrace_append hprefix tailTrace_5739108
  have hstable : (prefixWord ++ tailWord_5739108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739108).length < 2 ^ (prefixWord ++ tailWord_5739108).sum := by decide
  have hdescent : baseEnd_5739108 < baseStart_5739108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739118 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_5739118 : Nat := 118140960795 + 5739118 * 2 ^ 59
def prefixEnd_5739118 : Nat := 4983230072969 + 3 ^ 40 * 5739118 * 2
def baseEnd_5739118 : Nat := 2946926066870381908131283

theorem tailTrace_5739118 : CollatzResearch.WordTrace tailWord_5739118 prefixEnd_5739118 2946926066870381908131283 := by
  unfold tailWord_5739118
  simp only [CollatzResearch.WordTrace]
  refine ⟨26165353752770390520590251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139548553348108749443148005 26165353752770390520590251)
  ·
    refine ⟨39248030629155585780885377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26165353752770390520590251 39248030629155585780885377)
    ·
      refine ⟨29436022971866689335664033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39248030629155585780885377 29436022971866689335664033)
      ·
        refine ⟨22077017228900017001748025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29436022971866689335664033 22077017228900017001748025)
        ·
          refine ⟨16557762921675012751311019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22077017228900017001748025 16557762921675012751311019)
          ·
            refine ⟨24836644382512519126966529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16557762921675012751311019 24836644382512519126966529)
            ·
              refine ⟨18627483286884389345224897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24836644382512519126966529 18627483286884389345224897)
              ·
                refine ⟨13970612465163292008918673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18627483286884389345224897 13970612465163292008918673)
                ·
                  refine ⟨10477959348872469006689005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13970612465163292008918673 10477959348872469006689005)
                  ·
                    refine ⟨3929234755827175877508377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10477959348872469006689005 3929234755827175877508377)
                    ·
                      refine ⟨2946926066870381908131283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929234755827175877508377 2946926066870381908131283)
                      ·
                        rfl

theorem cell23_5739118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_5739118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739118 prefixEnd_5739118 := by exact prefixLift 5739118
  have htrace : WordTrace (prefixWord ++ tailWord_5739118) baseStart_5739118 baseEnd_5739118 := by
    simpa [prefixWord, tailWord_5739118, baseEnd_5739118] using wordTrace_append hprefix tailTrace_5739118
  have hstable : (prefixWord ++ tailWord_5739118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739118).length < 2 ^ (prefixWord ++ tailWord_5739118).sum := by decide
  have hdescent : baseEnd_5739118 < baseStart_5739118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739127 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_5739127 : Nat := 118140960795 + 5739127 * 2 ^ 59
def prefixEnd_5739127 : Nat := 4983230072969 + 3 ^ 40 * 5739127 * 2
def baseEnd_5739127 : Nat := 2946930688196272372918741

theorem tailTrace_5739127 : CollatzResearch.WordTrace tailWord_5739127 prefixEnd_5739127 2946930688196272372918741 := by
  unfold tailWord_5739127
  simp only [CollatzResearch.WordTrace]
  refine ⟨209323158279130518701799635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139548772186087012467866423 209323158279130518701799635)
  ·
    refine ⟨313984737418695778052699453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209323158279130518701799635 313984737418695778052699453)
    ·
      refine ⟨117744276532010916769762295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313984737418695778052699453 117744276532010916769762295)
      ·
        refine ⟨176616414798016375154643443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117744276532010916769762295 176616414798016375154643443)
        ·
          refine ⟨264924622197024562731965165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176616414798016375154643443 264924622197024562731965165)
          ·
            refine ⟨99346733323884211024486937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264924622197024562731965165 99346733323884211024486937)
            ·
              refine ⟨74510049992913158268365203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99346733323884211024486937 74510049992913158268365203)
              ·
                refine ⟨111765074989369737402547805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74510049992913158268365203 111765074989369737402547805)
                ·
                  refine ⟨41911903121013651525955427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111765074989369737402547805 41911903121013651525955427)
                  ·
                    refine ⟨62867854681520477288933141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41911903121013651525955427 62867854681520477288933141)
                    ·
                      refine ⟨2946930688196272372918741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62867854681520477288933141 2946930688196272372918741)
                      ·
                        rfl

theorem cell23_5739127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_5739127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739127 prefixEnd_5739127 := by exact prefixLift 5739127
  have htrace : WordTrace (prefixWord ++ tailWord_5739127) baseStart_5739127 baseEnd_5739127 := by
    simpa [prefixWord, tailWord_5739127, baseEnd_5739127] using wordTrace_append hprefix tailTrace_5739127
  have hstable : (prefixWord ++ tailWord_5739127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739127).length < 2 ^ (prefixWord ++ tailWord_5739127).sum := by decide
  have hdescent : baseEnd_5739127 < baseStart_5739127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739141 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_5739141 : Nat := 118140960795 + 5739141 * 2 ^ 59
def prefixEnd_5739141 : Nat := 4983230072969 + 3 ^ 40 * 5739141 * 2
def baseEnd_5739141 : Nat := 982312625641811772714559

theorem tailTrace_5739141 : CollatzResearch.WordTrace tailWord_5739141 prefixEnd_5739141 982312625641811772714559 := by
  unfold tailWord_5739141
  simp only [CollatzResearch.WordTrace]
  refine ⟨209323668901079799092809277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139549112600719866061872851 209323668901079799092809277)
  ·
    refine ⟨78496375837904924659803479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209323668901079799092809277 78496375837904924659803479)
    ·
      refine ⟨117744563756857386989705219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78496375837904924659803479 117744563756857386989705219)
      ·
        refine ⟨176616845635286080484557829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117744563756857386989705219 176616845635286080484557829)
        ·
          refine ⟨33115658556616140090854593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176616845635286080484557829 33115658556616140090854593)
          ·
            refine ⟨24836743917462105068140945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33115658556616140090854593 24836743917462105068140945)
            ·
              refine ⟨18627557938096578801105709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24836743917462105068140945 18627557938096578801105709)
              ·
                refine ⟨6985334226786217050414641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18627557938096578801105709 6985334226786217050414641)
                ·
                  refine ⟨5239000670089662787810981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6985334226786217050414641 5239000670089662787810981)
                  ·
                    refine ⟨982312625641811772714559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5239000670089662787810981 982312625641811772714559)
                    ·
                      rfl

theorem cell23_5739141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_5739141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739141 prefixEnd_5739141 := by exact prefixLift 5739141
  have htrace : WordTrace (prefixWord ++ tailWord_5739141) baseStart_5739141 baseEnd_5739141 := by
    simpa [prefixWord, tailWord_5739141, baseEnd_5739141] using wordTrace_append hprefix tailTrace_5739141
  have hstable : (prefixWord ++ tailWord_5739141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739141).length < 2 ^ (prefixWord ++ tailWord_5739141).sum := by decide
  have hdescent : baseEnd_5739141 < baseStart_5739141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739162 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_5739162 : Nat := 118140960795 + 5739162 * 2 ^ 59
def prefixEnd_5739162 : Nat := 4983230072969 + 3 ^ 40 * 5739162 * 2
def baseEnd_5739162 : Nat := 982316220006393245327027

theorem tailTrace_5739162 : CollatzResearch.WordTrace tailWord_5739162 prefixEnd_5739162 982316220006393245327027 := by
  unfold tailWord_5739162
  simp only [CollatzResearch.WordTrace]
  refine ⟨52331108708500929919830935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139549623222669146452882493 52331108708500929919830935)
  ·
    refine ⟨78496663062751394879746403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52331108708500929919830935 78496663062751394879746403)
    ·
      refine ⟨117744994594127092319619605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78496663062751394879746403 117744994594127092319619605)
      ·
        refine ⟨5519296621599707452482169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117744994594127092319619605 5519296621599707452482169)
        ·
          refine ⟨4139472466199780589361627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5519296621599707452482169 4139472466199780589361627)
          ·
            refine ⟨6209208699299670884042441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139472466199780589361627 6209208699299670884042441)
            ·
              refine ⟨4656906524474753163031831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209208699299670884042441 4656906524474753163031831)
              ·
                refine ⟨6985359786712129744547747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4656906524474753163031831 6985359786712129744547747)
                ·
                  refine ⟨10478039680068194616821621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6985359786712129744547747 10478039680068194616821621)
                  ·
                    refine ⟨982316220006393245327027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10478039680068194616821621 982316220006393245327027)
                    ·
                      rfl

theorem cell23_5739162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_5739162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739162 prefixEnd_5739162 := by exact prefixLift 5739162
  have htrace : WordTrace (prefixWord ++ tailWord_5739162) baseStart_5739162 baseEnd_5739162 := by
    simpa [prefixWord, tailWord_5739162, baseEnd_5739162] using wordTrace_append hprefix tailTrace_5739162
  have hstable : (prefixWord ++ tailWord_5739162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739162).length < 2 ^ (prefixWord ++ tailWord_5739162).sum := by decide
  have hdescent : baseEnd_5739162 < baseStart_5739162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739165 : List Nat := [1, 4, 2, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_5739165 : Nat := 118140960795 + 5739165 * 2 ^ 59
def prefixEnd_5739165 : Nat := 4983230072969 + 3 ^ 40 * 5739165 * 2
def baseEnd_5739165 : Nat := 2946950200461143224243567

theorem tailTrace_5739165 : CollatzResearch.WordTrace tailWord_5739165 prefixEnd_5739165 2946950200461143224243567 := by
  unfold tailWord_5739165
  simp only [CollatzResearch.WordTrace]
  refine ⟨209324544252992851191682949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139549696168661900794455299 209324544252992851191682949)
  ·
    refine ⟨39248352047436159598440553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209324544252992851191682949 39248352047436159598440553)
    ·
      refine ⟨29436264035577119698830415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39248352047436159598440553 29436264035577119698830415)
      ·
        refine ⟨44154396053365679548245623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29436264035577119698830415 44154396053365679548245623)
        ·
          refine ⟨66231594080048519322368435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44154396053365679548245623 66231594080048519322368435)
          ·
            refine ⟨99347391120072778983552653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66231594080048519322368435 99347391120072778983552653)
            ·
              refine ⟨37255271670027292118832245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99347391120072778983552653 37255271670027292118832245)
              ·
                refine ⟨3492681719065058636140523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37255271670027292118832245 3492681719065058636140523)
                ·
                  refine ⟨5239022578597587954210785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492681719065058636140523 5239022578597587954210785)
                  ·
                    refine ⟨3929266933948190965658089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239022578597587954210785 3929266933948190965658089)
                    ·
                      refine ⟨2946950200461143224243567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929266933948190965658089 2946950200461143224243567)
                      ·
                        rfl

theorem cell23_5739165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_5739165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739165 prefixEnd_5739165 := by exact prefixLift 5739165
  have htrace : WordTrace (prefixWord ++ tailWord_5739165) baseStart_5739165 baseEnd_5739165 := by
    simpa [prefixWord, tailWord_5739165, baseEnd_5739165] using wordTrace_append hprefix tailTrace_5739165
  have hstable : (prefixWord ++ tailWord_5739165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739165).length < 2 ^ (prefixWord ++ tailWord_5739165).sum := by decide
  have hdescent : baseEnd_5739165 < baseStart_5739165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739168 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3]
def baseStart_5739168 : Nat := 118140960795 + 5739168 * 2 ^ 59
def prefixEnd_5739168 : Nat := 4983230072969 + 3 ^ 40 * 5739168 * 2
def baseEnd_5739168 : Nat := 2946951740903106712506053

theorem tailTrace_5739168 : CollatzResearch.WordTrace tailWord_5739168 prefixEnd_5739168 2946951740903106712506053 := by
  unfold tailWord_5739168
  simp only [CollatzResearch.WordTrace]
  refine ⟨104662326835990991352021079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139549769114654655136028105 104662326835990991352021079)
  ·
    refine ⟨156993490253986487028031619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104662326835990991352021079 156993490253986487028031619)
    ·
      refine ⟨235490235380979730542047429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156993490253986487028031619 235490235380979730542047429)
      ·
        refine ⟨44154419133933699476633893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235490235380979730542047429 44154419133933699476633893)
        ·
          refine ⟨8278953587612568651868855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44154419133933699476633893 8278953587612568651868855)
          ·
            refine ⟨12418430381418852977803283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8278953587612568651868855 12418430381418852977803283)
            ·
              refine ⟨18627645572128279466704925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12418430381418852977803283 18627645572128279466704925)
              ·
                refine ⟨6985367089548104800014347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18627645572128279466704925 6985367089548104800014347)
                ·
                  refine ⟨10478050634322157200021521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6985367089548104800014347 10478050634322157200021521)
                  ·
                    refine ⟨7858537975741617900016141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10478050634322157200021521 7858537975741617900016141)
                    ·
                      refine ⟨2946951740903106712506053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858537975741617900016141 2946951740903106712506053)
                      ·
                        rfl

theorem cell23_5739168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_5739168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739168 prefixEnd_5739168 := by exact prefixLift 5739168
  have htrace : WordTrace (prefixWord ++ tailWord_5739168) baseStart_5739168 baseEnd_5739168 := by
    simpa [prefixWord, tailWord_5739168, baseEnd_5739168] using wordTrace_append hprefix tailTrace_5739168
  have hstable : (prefixWord ++ tailWord_5739168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739168).length < 2 ^ (prefixWord ++ tailWord_5739168).sum := by decide
  have hdescent : baseEnd_5739168 < baseStart_5739168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739182 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5739182 : Nat := 118140960795 + 5739182 * 2 ^ 59
def prefixEnd_5739182 : Nat := 4983230072969 + 3 ^ 40 * 5739182 * 2
def baseEnd_5739182 : Nat := 2946958929632269657730989

theorem tailTrace_5739182 : CollatzResearch.WordTrace tailWord_5739182 prefixEnd_5739182 2946958929632269657730989 := by
  unfold tailWord_5739182
  simp only [CollatzResearch.WordTrace]
  refine ⟨26165645536741407886881475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139550109529287508730034533 26165645536741407886881475)
  ·
    refine ⟨39248468305112111830322213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26165645536741407886881475 39248468305112111830322213)
    ·
      refine ⟨7359087807208520968185415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39248468305112111830322213 7359087807208520968185415)
      ·
        refine ⟨11038631710812781452278123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7359087807208520968185415 11038631710812781452278123)
        ·
          refine ⟨16557947566219172178417185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11038631710812781452278123 16557947566219172178417185)
          ·
            refine ⟨12418460674664379133812889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16557947566219172178417185 12418460674664379133812889)
            ·
              refine ⟨9313845505998284350359667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12418460674664379133812889 9313845505998284350359667)
              ·
                refine ⟨13970768258997426525539501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9313845505998284350359667 13970768258997426525539501)
                ·
                  refine ⟨5239038097124034947077313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13970768258997426525539501 5239038097124034947077313)
                  ·
                    refine ⟨3929278572843026210307985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239038097124034947077313 3929278572843026210307985)
                    ·
                      refine ⟨2946958929632269657730989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929278572843026210307985 2946958929632269657730989)
                      ·
                        rfl

theorem cell23_5739182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5739182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739182 prefixEnd_5739182 := by exact prefixLift 5739182
  have htrace : WordTrace (prefixWord ++ tailWord_5739182) baseStart_5739182 baseEnd_5739182 := by
    simpa [prefixWord, tailWord_5739182, baseEnd_5739182] using wordTrace_append hprefix tailTrace_5739182
  have hstable : (prefixWord ++ tailWord_5739182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739182).length < 2 ^ (prefixWord ++ tailWord_5739182).sum := by decide
  have hdescent : baseEnd_5739182 < baseStart_5739182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739208 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 1, 3, 2]
def baseStart_5739208 : Nat := 118140960795 + 5739208 * 2 ^ 59
def prefixEnd_5739208 : Nat := 4983230072969 + 3 ^ 40 * 5739208 * 2
def baseEnd_5739208 : Nat := 2946972280129286556005869

theorem tailTrace_5739208 : CollatzResearch.WordTrace tailWord_5739208 prefixEnd_5739208 2946972280129286556005869 := by
  unfold tailWord_5739208
  simp only [CollatzResearch.WordTrace]
  refine ⟨104663056295918534767749139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139550741727891379690332185 104663056295918534767749139)
  ·
    refine ⟨156994584443877802151623709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104663056295918534767749139 156994584443877802151623709)
    ·
      refine ⟨58872969166454175806858891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156994584443877802151623709 58872969166454175806858891)
      ·
        refine ⟨88309453749681263710288337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58872969166454175806858891 88309453749681263710288337)
        ·
          refine ⟨66232090312260947782716253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88309453749681263710288337 66232090312260947782716253)
          ·
            refine ⟨24837033867097855418518595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66232090312260947782716253 24837033867097855418518595)
            ·
              refine ⟨37255550800646783127777893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24837033867097855418518595 37255550800646783127777893)
              ·
                refine ⟨6985415775121271836458355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37255550800646783127777893 6985415775121271836458355)
                ·
                  refine ⟨10478123662681907754687533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6985415775121271836458355 10478123662681907754687533)
                  ·
                    refine ⟨3929296373505715408007825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10478123662681907754687533 3929296373505715408007825)
                    ·
                      refine ⟨2946972280129286556005869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929296373505715408007825 2946972280129286556005869)
                      ·
                        rfl

theorem cell23_5739208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_5739208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739208 prefixEnd_5739208 := by exact prefixLift 5739208
  have htrace : WordTrace (prefixWord ++ tailWord_5739208) baseStart_5739208 baseEnd_5739208 := by
    simpa [prefixWord, tailWord_5739208, baseEnd_5739208] using wordTrace_append hprefix tailTrace_5739208
  have hstable : (prefixWord ++ tailWord_5739208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739208).length < 2 ^ (prefixWord ++ tailWord_5739208).sum := by decide
  have hdescent : baseEnd_5739208 < baseStart_5739208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739224 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_5739224 : Nat := 118140960795 + 5739224 * 2 ^ 59
def prefixEnd_5739224 : Nat := 4983230072969 + 3 ^ 40 * 5739224 * 2
def baseEnd_5739224 : Nat := 2946980495819758493405795

theorem tailTrace_5739224 : CollatzResearch.WordTrace tailWord_5739224 prefixEnd_5739224 2946980495819758493405795 := by
  unfold tailWord_5739224
  simp only [CollatzResearch.WordTrace]
  refine ⟨104663348079889552134040363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139551130773186069512053817 104663348079889552134040363)
  ·
    refine ⟨156995022119834328201060545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104663348079889552134040363 156995022119834328201060545)
    ·
      refine ⟨117746266589875746150795409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156995022119834328201060545 117746266589875746150795409)
      ·
        refine ⟨88309699942406809613096557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117746266589875746150795409 88309699942406809613096557)
        ·
          refine ⟨33116137478402553604911209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88309699942406809613096557 33116137478402553604911209)
          ·
            refine ⟨24837103108801915203683407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33116137478402553604911209 24837103108801915203683407)
            ·
              refine ⟨37255654663202872805525111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24837103108801915203683407 37255654663202872805525111)
              ·
                refine ⟨55883481994804309208287667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37255654663202872805525111 55883481994804309208287667)
                ·
                  refine ⟨83825222992206463812431501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55883481994804309208287667 83825222992206463812431501)
                  ·
                    refine ⟨31434458622077423929661813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83825222992206463812431501 31434458622077423929661813)
                    ·
                      refine ⟨2946980495819758493405795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31434458622077423929661813 2946980495819758493405795)
                      ·
                        rfl

theorem cell23_5739224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_5739224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739224 prefixEnd_5739224 := by exact prefixLift 5739224
  have htrace : WordTrace (prefixWord ++ tailWord_5739224) baseStart_5739224 baseEnd_5739224 := by
    simpa [prefixWord, tailWord_5739224, baseEnd_5739224] using wordTrace_append hprefix tailTrace_5739224
  have hstable : (prefixWord ++ tailWord_5739224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739224).length < 2 ^ (prefixWord ++ tailWord_5739224).sum := by decide
  have hdescent : baseEnd_5739224 < baseStart_5739224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739295 : List Nat := [1, 1, 2, 4, 2, 4, 2, 2, 5]
def baseStart_5739295 : Nat := 118140960795 + 5739295 * 2 ^ 59
def prefixEnd_5739295 : Nat := 4983230072969 + 3 ^ 40 * 5739295 * 2
def baseEnd_5739295 : Nat := 327446328105136412846441

theorem tailTrace_5739295 : CollatzResearch.WordTrace tailWord_5739295 prefixEnd_5739295 327446328105136412846441 := by
  unfold tailWord_5739295
  simp only [CollatzResearch.WordTrace]
  refine ⟨209329285742521883393915339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139552857161681255595943559 209329285742521883393915339)
  ·
    refine ⟨313993928613782825090873009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209329285742521883393915339 313993928613782825090873009)
    ·
      refine ⟨235495446460337118818154757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313993928613782825090873009 235495446460337118818154757)
      ·
        refine ⟨44155396211313209778404017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235495446460337118818154757 44155396211313209778404017)
        ·
          refine ⟨33116547158484907333803013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44155396211313209778404017 33116547158484907333803013)
          ·
            refine ⟨6209352592215920125088065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33116547158484907333803013 6209352592215920125088065)
            ·
              refine ⟨4657014444161940093816049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209352592215920125088065 4657014444161940093816049)
              ·
                refine ⟨3492760833121455070362037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657014444161940093816049 3492760833121455070362037)
                ·
                  refine ⟨327446328105136412846441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3492760833121455070362037 327446328105136412846441)
                  ·
                    rfl

theorem cell23_5739295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 5].length) (baseStart_5739295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739295 prefixEnd_5739295 := by exact prefixLift 5739295
  have htrace : WordTrace (prefixWord ++ tailWord_5739295) baseStart_5739295 baseEnd_5739295 := by
    simpa [prefixWord, tailWord_5739295, baseEnd_5739295] using wordTrace_append hprefix tailTrace_5739295
  have hstable : (prefixWord ++ tailWord_5739295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739295).length < 2 ^ (prefixWord ++ tailWord_5739295).sum := by decide
  have hdescent : baseEnd_5739295 < baseStart_5739295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739298 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_5739298 : Nat := 118140960795 + 5739298 * 2 ^ 59
def prefixEnd_5739298 : Nat := 4983230072969 + 3 ^ 40 * 5739298 * 2
def baseEnd_5739298 : Nat := 2947018493388191203880455

theorem tailTrace_5739298 : CollatzResearch.WordTrace tailWord_5739298 prefixEnd_5739298 2947018493388191203880455 := by
  unfold tailWord_5739298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52332348790377753726568637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139552930107674009937516365 52332348790377753726568637)
  ·
    refine ⟨19624630796391657647463239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52332348790377753726568637 19624630796391657647463239)
    ·
      refine ⟨29436946194587486471194859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19624630796391657647463239 29436946194587486471194859)
      ·
        refine ⟨44155419291881229706792289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29436946194587486471194859 44155419291881229706792289)
        ·
          refine ⟨33116564468910922280094217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44155419291881229706792289 33116564468910922280094217)
          ·
            refine ⟨24837423351683191710070663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33116564468910922280094217 24837423351683191710070663)
            ·
              refine ⟨37256135027524787565105995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24837423351683191710070663 37256135027524787565105995)
              ·
                refine ⟨55884202541287181347658993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37256135027524787565105995 55884202541287181347658993)
                ·
                  refine ⟨41913151905965386010744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55884202541287181347658993 41913151905965386010744245)
                  ·
                    refine ⟨3929357991184254938507273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41913151905965386010744245 3929357991184254938507273)
                    ·
                      refine ⟨2947018493388191203880455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929357991184254938507273 2947018493388191203880455)
                      ·
                        rfl

theorem cell23_5739298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_5739298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739298 prefixEnd_5739298 := by exact prefixLift 5739298
  have htrace : WordTrace (prefixWord ++ tailWord_5739298) baseStart_5739298 baseEnd_5739298 := by
    simpa [prefixWord, tailWord_5739298, baseEnd_5739298] using wordTrace_append hprefix tailTrace_5739298
  have hstable : (prefixWord ++ tailWord_5739298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739298).length < 2 ^ (prefixWord ++ tailWord_5739298).sum := by decide
  have hdescent : baseEnd_5739298 < baseStart_5739298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739325 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_5739325 : Nat := 118140960795 + 5739325 * 2 ^ 59
def prefixEnd_5739325 : Nat := 4983230072969 + 3 ^ 40 * 5739325 * 2
def baseEnd_5739325 : Nat := 982344119121954199414277

theorem tailTrace_5739325 : CollatzResearch.WordTrace tailWord_5739325 prefixEnd_5739325 982344119121954199414277 := by
  unfold tailWord_5739325
  simp only [CollatzResearch.WordTrace]
  refine ⟨209330379932413198517507429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139553586621608799011671619 209330379932413198517507429)
  ·
    refine ⟨39249446237327474722032643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209330379932413198517507429 39249446237327474722032643)
    ·
      refine ⟨58874169355991212083048965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39249446237327474722032643 58874169355991212083048965)
      ·
        refine ⟨11038906754248352265571681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58874169355991212083048965 11038906754248352265571681)
        ·
          refine ⟨8279180065686264199178761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11038906754248352265571681 8279180065686264199178761)
          ·
            refine ⟨6209385049264698149384071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8279180065686264199178761 6209385049264698149384071)
            ·
              refine ⟨9314077573897047224076107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209385049264698149384071 9314077573897047224076107)
              ·
                refine ⟨13971116360845570836114161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9314077573897047224076107 13971116360845570836114161)
                ·
                  refine ⟨10478337270634178127085621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13971116360845570836114161 10478337270634178127085621)
                  ·
                    refine ⟨982344119121954199414277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10478337270634178127085621 982344119121954199414277)
                    ·
                      rfl

theorem cell23_5739325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_5739325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739325 prefixEnd_5739325 := by exact prefixLift 5739325
  have htrace : WordTrace (prefixWord ++ tailWord_5739325) baseStart_5739325 baseEnd_5739325 := by
    simpa [prefixWord, tailWord_5739325, baseEnd_5739325] using wordTrace_append hprefix tailTrace_5739325
  have hstable : (prefixWord ++ tailWord_5739325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739325).length < 2 ^ (prefixWord ++ tailWord_5739325).sum := by decide
  have hdescent : baseEnd_5739325 < baseStart_5739325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739331 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 3]
def baseStart_5739331 : Nat := 118140960795 + 5739331 * 2 ^ 59
def prefixEnd_5739331 : Nat := 4983230072969 + 3 ^ 40 * 5739331 * 2
def baseEnd_5739331 : Nat := 2947035438249789574767803

theorem tailTrace_5739331 : CollatzResearch.WordTrace tailWord_5739331 prefixEnd_5739331 2947035438249789574767803 := by
  unfold tailWord_5739331
  simp only [CollatzResearch.WordTrace]
  refine ⟨209330598770391461542225847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139553732513594307694817231 209330598770391461542225847)
  ·
    refine ⟨313995898155587192313338771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209330598770391461542225847 313995898155587192313338771)
    ·
      refine ⟨470993847233380788470008157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313995898155587192313338771 470993847233380788470008157)
      ·
        refine ⟨176622692712517795676253059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470993847233380788470008157 176622692712517795676253059)
        ·
          refine ⟨264934039068776693514379589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176622692712517795676253059 264934039068776693514379589)
          ·
            refine ⟨49675132325395630033946173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264934039068776693514379589 49675132325395630033946173)
            ·
              refine ⟨18628174622023361262729815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49675132325395630033946173 18628174622023361262729815)
              ·
                refine ⟨27942261933035041894094723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18628174622023361262729815 27942261933035041894094723)
                ·
                  refine ⟨41913392899552562841142085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27942261933035041894094723 41913392899552562841142085)
                  ·
                    refine ⟨7858761168666105532714141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41913392899552562841142085 7858761168666105532714141)
                    ·
                      refine ⟨2947035438249789574767803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858761168666105532714141 2947035438249789574767803)
                      ·
                        rfl

theorem cell23_5739331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_5739331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739331 prefixEnd_5739331 := by exact prefixLift 5739331
  have htrace : WordTrace (prefixWord ++ tailWord_5739331) baseStart_5739331 baseEnd_5739331 := by
    simpa [prefixWord, tailWord_5739331, baseEnd_5739331] using wordTrace_append hprefix tailTrace_5739331
  have hstable : (prefixWord ++ tailWord_5739331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739331).length < 2 ^ (prefixWord ++ tailWord_5739331).sum := by decide
  have hdescent : baseEnd_5739331 < baseStart_5739331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739351 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 8]
def baseStart_5739351 : Nat := 118140960795 + 5739351 * 2 ^ 59
def prefixEnd_5739351 : Nat := 4983230072969 + 3 ^ 40 * 5739351 * 2
def baseEnd_5739351 : Nat := 327449523095875499613079

theorem tailTrace_5739351 : CollatzResearch.WordTrace tailWord_5739351 prefixEnd_5739351 327449523095875499613079 := by
  unfold tailWord_5739351
  simp only [CollatzResearch.WordTrace]
  refine ⟨209331328230319004957953907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139554218820212669971969271 209331328230319004957953907)
  ·
    refine ⟨313996992345478507436930861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209331328230319004957953907 313996992345478507436930861)
    ·
      refine ⟨117748872129554440288849073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313996992345478507436930861 117748872129554440288849073)
      ·
        refine ⟨88311654097165830216636805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117748872129554440288849073 88311654097165830216636805)
        ·
          refine ⟨16558435143218593165619401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88311654097165830216636805 16558435143218593165619401)
          ·
            refine ⟨12418826357413944874214551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16558435143218593165619401 12418826357413944874214551)
            ·
              refine ⟨18628239536120917311321827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12418826357413944874214551 18628239536120917311321827)
              ·
                refine ⟨27942359304181375966982741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18628239536120917311321827 27942359304181375966982741)
                ·
                  refine ⟨327449523095875499613079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27942359304181375966982741 327449523095875499613079)
                  ·
                    rfl

theorem cell23_5739351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 8].length) (baseStart_5739351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739351 prefixEnd_5739351 := by exact prefixLift 5739351
  have htrace : WordTrace (prefixWord ++ tailWord_5739351) baseStart_5739351 baseEnd_5739351 := by
    simpa [prefixWord, tailWord_5739351, baseEnd_5739351] using wordTrace_append hprefix tailTrace_5739351
  have hstable : (prefixWord ++ tailWord_5739351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739351).length < 2 ^ (prefixWord ++ tailWord_5739351).sum := by decide
  have hdescent : baseEnd_5739351 < baseStart_5739351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739388 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_5739388 : Nat := 118140960795 + 5739388 * 2 ^ 59
def prefixEnd_5739388 : Nat := 4983230072969 + 3 ^ 40 * 5739388 * 2
def baseEnd_5739388 : Nat := 2947064706647095851755041

theorem tailTrace_5739388 : CollatzResearch.WordTrace tailWord_5739388 prefixEnd_5739388 2947064706647095851755041 := by
  unfold tailWord_5739388
  simp only [CollatzResearch.WordTrace]
  refine ⟨104666338865592480138525409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139555118487456640184700545 104666338865592480138525409)
  ·
    refine ⟨78499754149194360103894057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104666338865592480138525409 78499754149194360103894057)
    ·
      refine ⟨58874815611895770077920543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78499754149194360103894057 58874815611895770077920543)
      ·
        refine ⟨88312223417843655116880815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58874815611895770077920543 88312223417843655116880815)
        ·
          refine ⟨132468335126765482675321223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88312223417843655116880815 132468335126765482675321223)
          ·
            refine ⟨198702502690148224012981835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132468335126765482675321223 198702502690148224012981835)
            ·
              refine ⟨298053754035222336019472753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198702502690148224012981835 298053754035222336019472753)
              ·
                refine ⟨223540315526416752014604565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298053754035222336019472753 223540315526416752014604565)
                ·
                  refine ⟨10478452290300785250684589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223540315526416752014604565 10478452290300785250684589)
                  ·
                    refine ⟨3929419608862794469006721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10478452290300785250684589 3929419608862794469006721)
                    ·
                      refine ⟨2947064706647095851755041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929419608862794469006721 2947064706647095851755041)
                      ·
                        rfl

theorem cell23_5739388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_5739388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739388 prefixEnd_5739388 := by exact prefixLift 5739388
  have htrace : WordTrace (prefixWord ++ tailWord_5739388) baseStart_5739388 baseEnd_5739388 := by
    simpa [prefixWord, tailWord_5739388, baseEnd_5739388] using wordTrace_append hprefix tailTrace_5739388
  have hstable : (prefixWord ++ tailWord_5739388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739388).length < 2 ^ (prefixWord ++ tailWord_5739388).sum := by decide
  have hdescent : baseEnd_5739388 < baseStart_5739388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739448 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_5739448 : Nat := 118140960795 + 5739448 * 2 ^ 59
def prefixEnd_5739448 : Nat := 4983230072969 + 3 ^ 40 * 5739448 * 2
def baseEnd_5739448 : Nat := 2947095515486365617004765

theorem tailTrace_5739448 : CollatzResearch.WordTrace tailWord_5739448 prefixEnd_5739448 2947095515486365617004765 := by
  unfold tailWord_5739448
  simp only [CollatzResearch.WordTrace]
  refine ⟨104667433055483795262117499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139556577407311727016156665 104667433055483795262117499)
  ·
    refine ⟨157001149583225692893176249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104667433055483795262117499 157001149583225692893176249)
    ·
      refine ⟨117750862187419269669882187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157001149583225692893176249 117750862187419269669882187)
      ·
        refine ⟨176626293281128904504823281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117750862187419269669882187 176626293281128904504823281)
        ·
          refine ⟨132469719960846678378617461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176626293281128904504823281 132469719960846678378617461)
          ·
            refine ⟨12419036246329376097995387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132469719960846678378617461 12419036246329376097995387)
            ·
              refine ⟨18628554369494064146993081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12419036246329376097995387 18628554369494064146993081)
              ·
                refine ⟨13971415777120548110244811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18628554369494064146993081 13971415777120548110244811)
                ·
                  refine ⟨20957123665680822165367217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13971415777120548110244811 20957123665680822165367217)
                  ·
                    refine ⟨15717842749260616624025413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20957123665680822165367217 15717842749260616624025413)
                    ·
                      refine ⟨2947095515486365617004765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15717842749260616624025413 2947095515486365617004765)
                      ·
                        rfl

theorem cell23_5739448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_5739448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739448 prefixEnd_5739448 := by exact prefixLift 5739448
  have htrace : WordTrace (prefixWord ++ tailWord_5739448) baseStart_5739448 baseEnd_5739448 := by
    simpa [prefixWord, tailWord_5739448, baseEnd_5739448] using wordTrace_append hprefix tailTrace_5739448
  have hstable : (prefixWord ++ tailWord_5739448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739448).length < 2 ^ (prefixWord ++ tailWord_5739448).sum := by decide
  have hdescent : baseEnd_5739448 < baseStart_5739448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739451 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 3]
def baseStart_5739451 : Nat := 118140960795 + 5739451 * 2 ^ 59
def prefixEnd_5739451 : Nat := 4983230072969 + 3 ^ 40 * 5739451 * 2
def baseEnd_5739451 : Nat := 2947097055928329105267251

theorem tailTrace_5739451 : CollatzResearch.WordTrace tailWord_5739451 prefixEnd_5739451 2947097055928329105267251 := by
  unfold tailWord_5739451
  simp only [CollatzResearch.WordTrace]
  refine ⟨209334975529956722036594207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139556650353304481357729471 209334975529956722036594207)
  ·
    refine ⟨314002463294935083054891311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209334975529956722036594207 314002463294935083054891311)
    ·
      refine ⟨471003694942402624582336967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314002463294935083054891311 471003694942402624582336967)
      ·
        refine ⟨706505542413603936873505451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471003694942402624582336967 706505542413603936873505451)
        ·
          refine ⟨1059758313620405905310258177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706505542413603936873505451 1059758313620405905310258177)
          ·
            refine ⟨794818735215304428982693633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1059758313620405905310258177 794818735215304428982693633)
            ·
              refine ⟨596114051411478321737020225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794818735215304428982693633 596114051411478321737020225)
              ·
                refine ⟨447085538558608741302765169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596114051411478321737020225 447085538558608741302765169)
                ·
                  refine ⟨335314153918956555977073877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447085538558608741302765169 335314153918956555977073877)
                  ·
                    refine ⟨7858925482475544280712669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 335314153918956555977073877 7858925482475544280712669)
                    ·
                      refine ⟨2947097055928329105267251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858925482475544280712669 2947097055928329105267251)
                      ·
                        rfl

theorem cell23_5739451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 3].length) (baseStart_5739451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739451 prefixEnd_5739451 := by exact prefixLift 5739451
  have htrace : WordTrace (prefixWord ++ tailWord_5739451) baseStart_5739451 baseEnd_5739451 := by
    simpa [prefixWord, tailWord_5739451, baseEnd_5739451] using wordTrace_append hprefix tailTrace_5739451
  have hstable : (prefixWord ++ tailWord_5739451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739451).length < 2 ^ (prefixWord ++ tailWord_5739451).sum := by decide
  have hdescent : baseEnd_5739451 < baseStart_5739451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739468 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_5739468 : Nat := 118140960795 + 5739468 * 2 ^ 59
def prefixEnd_5739468 : Nat := 4983230072969 + 3 ^ 40 * 5739468 * 2
def baseEnd_5739468 : Nat := 2947105785099455538754673

theorem tailTrace_5739468 : CollatzResearch.WordTrace tailWord_5739468 prefixEnd_5739468 2947105785099455538754673 := by
  unfold tailWord_5739468
  simp only [CollatzResearch.WordTrace]
  refine ⟨104667797785447566969981529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139557063713930089293308705 104667797785447566969981529)
  ·
    refine ⟨78500848339085675227486147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104667797785447566969981529 78500848339085675227486147)
    ·
      refine ⟨117751272508628512841229221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78500848339085675227486147 117751272508628512841229221)
      ·
        refine ⟨22078363595367846157730479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117751272508628512841229221 22078363595367846157730479)
        ·
          refine ⟨33117545393051769236595719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22078363595367846157730479 33117545393051769236595719)
          ·
            refine ⟨49676318089577653854893579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33117545393051769236595719 49676318089577653854893579)
            ·
              refine ⟨74514477134366480782340369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49676318089577653854893579 74514477134366480782340369)
              ·
                refine ⟨55885857850774860586755277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74514477134366480782340369 55885857850774860586755277)
                ·
                  refine ⟨20957196694040572720033229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55885857850774860586755277 20957196694040572720033229)
                  ·
                    refine ⟨7858948760265214770012461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20957196694040572720033229 7858948760265214770012461)
                    ·
                      refine ⟨2947105785099455538754673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858948760265214770012461 2947105785099455538754673)
                      ·
                        rfl

theorem cell23_5739468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_5739468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739468 prefixEnd_5739468 := by exact prefixLift 5739468
  have htrace : WordTrace (prefixWord ++ tailWord_5739468) baseStart_5739468 baseEnd_5739468 := by
    simpa [prefixWord, tailWord_5739468, baseEnd_5739468] using wordTrace_append hprefix tailTrace_5739468
  have hstable : (prefixWord ++ tailWord_5739468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739468).length < 2 ^ (prefixWord ++ tailWord_5739468).sum := by decide
  have hdescent : baseEnd_5739468 < baseStart_5739468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739471 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 2, 7]
def baseStart_5739471 : Nat := 118140960795 + 5739471 * 2 ^ 59
def prefixEnd_5739471 : Nat := 4983230072969 + 3 ^ 40 * 5739471 * 2
def baseEnd_5739471 : Nat := 982369108513806342339053

theorem tailTrace_5739471 : CollatzResearch.WordTrace tailWord_5739471 prefixEnd_5739471 982369108513806342339053 := by
  unfold tailWord_5739471
  simp only [CollatzResearch.WordTrace]
  refine ⟨209335704989884265452322267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139557136659922843634881511 209335704989884265452322267)
  ·
    refine ⟨314003557484826398178483401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209335704989884265452322267 314003557484826398178483401)
    ·
      refine ⟨235502668113619798633862551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314003557484826398178483401 235502668113619798633862551)
      ·
        refine ⟨353254002170429697950793827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235502668113619798633862551 353254002170429697950793827)
        ·
          refine ⟨529881003255644546926190741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353254002170429697950793827 529881003255644546926190741)
          ·
            refine ⟨24838172027608338137165191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 529881003255644546926190741 24838172027608338137165191)
            ·
              refine ⟨37257258041412507205747787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24838172027608338137165191 37257258041412507205747787)
              ·
                refine ⟨55885887062118760808621681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37257258041412507205747787 55885887062118760808621681)
                ·
                  refine ⟨41914415296589070606466261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55885887062118760808621681 41914415296589070606466261)
                  ·
                    refine ⟨982369108513806342339053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41914415296589070606466261 982369108513806342339053)
                    ·
                      rfl

theorem cell23_5739471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_5739471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739471 prefixEnd_5739471 := by exact prefixLift 5739471
  have htrace : WordTrace (prefixWord ++ tailWord_5739471) baseStart_5739471 baseEnd_5739471 := by
    simpa [prefixWord, tailWord_5739471, baseEnd_5739471] using wordTrace_append hprefix tailTrace_5739471
  have hstable : (prefixWord ++ tailWord_5739471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739471).length < 2 ^ (prefixWord ++ tailWord_5739471).sum := by decide
  have hdescent : baseEnd_5739471 < baseStart_5739471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739485 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5739485 : Nat := 118140960795 + 5739485 * 2 ^ 59
def prefixEnd_5739485 : Nat := 4983230072969 + 3 ^ 40 * 5739485 * 2
def baseEnd_5739485 : Nat := 2947114514270581972242095

theorem tailTrace_5739485 : CollatzResearch.WordTrace tailWord_5739485 prefixEnd_5739485 2947114514270581972242095 := by
  unfold tailWord_5739485
  simp only [CollatzResearch.WordTrace]
  refine ⟨209336215611833545843331909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139557477074555697228887939 209336215611833545843331909)
  ·
    refine ⟨39250540427218789845624733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209336215611833545843331909 39250540427218789845624733)
    ·
      refine ⟨14718952660207046192109275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39250540427218789845624733 14718952660207046192109275)
      ·
        refine ⟨22078428990310569288163913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14718952660207046192109275 22078428990310569288163913)
        ·
          refine ⟨16558821742732926966122935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22078428990310569288163913 16558821742732926966122935)
          ·
            refine ⟨24838232614099390449184403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16558821742732926966122935 24838232614099390449184403)
            ·
              refine ⟨37257348921149085673776605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24838232614099390449184403 37257348921149085673776605)
              ·
                refine ⟨13971505845430907127666227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37257348921149085673776605 13971505845430907127666227)
                ·
                  refine ⟨20957258768146360691499341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13971505845430907127666227 20957258768146360691499341)
                  ·
                    refine ⟨7858972038054885259312253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20957258768146360691499341 7858972038054885259312253)
                    ·
                      refine ⟨2947114514270581972242095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7858972038054885259312253 2947114514270581972242095)
                      ·
                        rfl

theorem cell23_5739485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5739485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739485 prefixEnd_5739485 := by exact prefixLift 5739485
  have htrace : WordTrace (prefixWord ++ tailWord_5739485) baseStart_5739485 baseEnd_5739485 := by
    simpa [prefixWord, tailWord_5739485, baseEnd_5739485] using wordTrace_append hprefix tailTrace_5739485
  have hstable : (prefixWord ++ tailWord_5739485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739485).length < 2 ^ (prefixWord ++ tailWord_5739485).sum := by decide
  have hdescent : baseEnd_5739485 < baseStart_5739485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739506 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5739506 : Nat := 118140960795 + 5739506 * 2 ^ 59
def prefixEnd_5739506 : Nat := 4983230072969 + 3 ^ 40 * 5739506 * 2
def baseEnd_5739506 : Nat := 2947125297364326390079499

theorem tailTrace_5739506 : CollatzResearch.WordTrace tailWord_5739506 prefixEnd_5739506 2947125297364326390079499 := by
  unfold tailWord_5739506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52334245386189366607461593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139557987696504977619897581 52334245386189366607461593)
  ·
    refine ⟨39250684039642024955596195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52334245386189366607461593 39250684039642024955596195)
    ·
      refine ⟨58876026059463037433394293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39250684039642024955596195 58876026059463037433394293)
      ·
        refine ⟨5519627443074659759380715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58876026059463037433394293 5519627443074659759380715)
        ·
          refine ⟨8279441164611989639071073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5519627443074659759380715 8279441164611989639071073)
          ·
            refine ⟨6209580873458992229303305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8279441164611989639071073 6209580873458992229303305)
            ·
              refine ⟨4657185655094244171977479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209580873458992229303305 4657185655094244171977479)
              ·
                refine ⟨6985778482641366257966219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657185655094244171977479 6985778482641366257966219)
                ·
                  refine ⟨10478667723962049386949329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6985778482641366257966219 10478667723962049386949329)
                  ·
                    refine ⟨7859000792971537040211997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10478667723962049386949329 7859000792971537040211997)
                    ·
                      refine ⟨2947125297364326390079499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7859000792971537040211997 2947125297364326390079499)
                      ·
                        rfl

theorem cell23_5739506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5739506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739506 prefixEnd_5739506 := by exact prefixLift 5739506
  have htrace : WordTrace (prefixWord ++ tailWord_5739506) baseStart_5739506 baseEnd_5739506 := by
    simpa [prefixWord, tailWord_5739506, baseEnd_5739506] using wordTrace_append hprefix tailTrace_5739506
  have hstable : (prefixWord ++ tailWord_5739506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739506).length < 2 ^ (prefixWord ++ tailWord_5739506).sum := by decide
  have hdescent : baseEnd_5739506 < baseStart_5739506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739559 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5739559 : Nat := 118140960795 + 5739559 * 2 ^ 59
def prefixEnd_5739559 : Nat := 4983230072969 + 3 ^ 40 * 5739559 * 2
def baseEnd_5739559 : Nat := 2947152511839014682716755

theorem tailTrace_5739559 : CollatzResearch.WordTrace tailWord_5739559 prefixEnd_5739559 2947152511839014682716755 := by
  unfold tailWord_5739559
  simp only [CollatzResearch.WordTrace]
  refine ⟨209338914613565456481525731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139559276409043637654350487 209338914613565456481525731)
  ·
    refine ⟨314008371920348184722288597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209338914613565456481525731 314008371920348184722288597)
    ·
      refine ⟨7359571216883160579428639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 314008371920348184722288597 7359571216883160579428639)
      ·
        refine ⟨11039356825324740869142959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7359571216883160579428639 11039356825324740869142959)
        ·
          refine ⟨16559035237987111303714439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039356825324740869142959 16559035237987111303714439)
          ·
            refine ⟨24838552856980666955571659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16559035237987111303714439 24838552856980666955571659)
            ·
              refine ⟨37257829285471000433357489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24838552856980666955571659 37257829285471000433357489)
              ·
                refine ⟨27943371964103250325018117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37257829285471000433357489 27943371964103250325018117)
                ·
                  refine ⟨5239382243269359435940897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27943371964103250325018117 5239382243269359435940897)
                  ·
                    refine ⟨3929536682452019576955673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239382243269359435940897 3929536682452019576955673)
                    ·
                      refine ⟨2947152511839014682716755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929536682452019576955673 2947152511839014682716755)
                      ·
                        rfl

theorem cell23_5739559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5739559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739559 prefixEnd_5739559 := by exact prefixLift 5739559
  have htrace : WordTrace (prefixWord ++ tailWord_5739559) baseStart_5739559 baseEnd_5739559 := by
    simpa [prefixWord, tailWord_5739559, baseEnd_5739559] using wordTrace_append hprefix tailTrace_5739559
  have hstable : (prefixWord ++ tailWord_5739559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739559).length < 2 ^ (prefixWord ++ tailWord_5739559).sum := by decide
  have hdescent : baseEnd_5739559 < baseStart_5739559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739578 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_5739578 : Nat := 118140960795 + 5739578 * 2 ^ 59
def prefixEnd_5739578 : Nat := 4983230072969 + 3 ^ 40 * 5739578 * 2
def baseEnd_5739578 : Nat := 982387422657150036126389

theorem tailTrace_5739578 : CollatzResearch.WordTrace tailWord_5739578 prefixEnd_5739578 982387422657150036126389 := by
  unfold tailWord_5739578
  simp only [CollatzResearch.WordTrace]
  refine ⟨52334901900124155681616847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139559738400331081817644925 52334901900124155681616847)
  ·
    refine ⟨78502352850186233522425271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52334901900124155681616847 78502352850186233522425271)
    ·
      refine ⟨117753529275279350283637907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78502352850186233522425271 117753529275279350283637907)
      ·
        refine ⟨176630293912919025425456861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117753529275279350283637907 176630293912919025425456861)
        ·
          refine ⟨66236360217344634534546323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176630293912919025425456861 66236360217344634534546323)
          ·
            refine ⟨99354540326016951801819485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66236360217344634534546323 99354540326016951801819485)
            ·
              refine ⟨37257952622256356925682307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99354540326016951801819485 37257952622256356925682307)
              ·
                refine ⟨55886928933384535388523461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37257952622256356925682307 55886928933384535388523461)
                ·
                  refine ⟨10478799175009600385348149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55886928933384535388523461 10478799175009600385348149)
                  ·
                    refine ⟨982387422657150036126389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10478799175009600385348149 982387422657150036126389)
                    ·
                      rfl

theorem cell23_5739578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_5739578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739578 prefixEnd_5739578 := by exact prefixLift 5739578
  have htrace : WordTrace (prefixWord ++ tailWord_5739578) baseStart_5739578 baseEnd_5739578 := by
    simpa [prefixWord, tailWord_5739578, baseEnd_5739578] using wordTrace_append hprefix tailTrace_5739578
  have hstable : (prefixWord ++ tailWord_5739578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739578).length < 2 ^ (prefixWord ++ tailWord_5739578).sum := by decide
  have hdescent : baseEnd_5739578 < baseStart_5739578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739582 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 7]
def baseStart_5739582 : Nat := 118140960795 + 5739582 * 2 ^ 59
def prefixEnd_5739582 : Nat := 4983230072969 + 3 ^ 40 * 5739582 * 2
def baseEnd_5739582 : Nat := 327462702432674232525461

theorem tailTrace_5739582 : CollatzResearch.WordTrace tailWord_5739582 prefixEnd_5739582 327462702432674232525461 := by
  unfold tailWord_5739582
  simp only [CollatzResearch.WordTrace]
  refine ⟨26167469186560266426201625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139559835661654754273075333 26167469186560266426201625)
  ·
    refine ⟨19625601889920199819651219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26167469186560266426201625 19625601889920199819651219)
    ·
      refine ⟨29438402834880299729476829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19625601889920199819651219 29438402834880299729476829)
      ·
        refine ⟨11039401063080112398553811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29438402834880299729476829 11039401063080112398553811)
        ·
          refine ⟨16559101594620168597830717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039401063080112398553811 16559101594620168597830717)
          ·
            refine ⟨6209663097982563224186519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16559101594620168597830717 6209663097982563224186519)
            ·
              refine ⟨9314494646973844836279779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209663097982563224186519 9314494646973844836279779)
              ·
                refine ⟨13971741970460767254419669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9314494646973844836279779 13971741970460767254419669)
                ·
                  refine ⟨327462702432674232525461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13971741970460767254419669 327462702432674232525461)
                  ·
                    rfl

theorem cell23_5739582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_5739582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739582 prefixEnd_5739582 := by exact prefixLift 5739582
  have htrace : WordTrace (prefixWord ++ tailWord_5739582) baseStart_5739582 baseEnd_5739582 := by
    simpa [prefixWord, tailWord_5739582, baseEnd_5739582] using wordTrace_append hprefix tailTrace_5739582
  have hstable : (prefixWord ++ tailWord_5739582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739582).length < 2 ^ (prefixWord ++ tailWord_5739582).sum := by decide
  have hdescent : baseEnd_5739582 < baseStart_5739582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739615 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 4]
def baseStart_5739615 : Nat := 118140960795 + 5739615 * 2 ^ 59
def prefixEnd_5739615 : Nat := 4983230072969 + 3 ^ 40 * 5739615 * 2
def baseEnd_5739615 : Nat := 2947181266755666463616497

theorem tailTrace_5739615 : CollatzResearch.WordTrace tailWord_5739615 prefixEnd_5739615 2947181266755666463616497 := by
  unfold tailWord_5739615
  simp only [CollatzResearch.WordTrace]
  refine ⟨209340957101362578045564299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139560638067575052030376199 209340957101362578045564299)
  ·
    refine ⟨314011435652043867068346449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209340957101362578045564299 314011435652043867068346449)
    ·
      refine ⟨235508576739032900301259837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314011435652043867068346449 235508576739032900301259837)
      ·
        refine ⟨88315716277137337612972439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235508576739032900301259837 88315716277137337612972439)
        ·
          refine ⟨132473574415706006419458659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88315716277137337612972439 132473574415706006419458659)
          ·
            refine ⟨198710361623559009629187989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132473574415706006419458659 198710361623559009629187989)
            ·
              refine ⟨9314548201104328576368187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198710361623559009629187989 9314548201104328576368187)
              ·
                refine ⟨13971822301656492864552281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9314548201104328576368187 13971822301656492864552281)
                ·
                  refine ⟨10478866726242369648414211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13971822301656492864552281 10478866726242369648414211)
                  ·
                    refine ⟨15718300089363554472621317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10478866726242369648414211 15718300089363554472621317)
                    ·
                      refine ⟨2947181266755666463616497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15718300089363554472621317 2947181266755666463616497)
                      ·
                        rfl

theorem cell23_5739615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_5739615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739615 prefixEnd_5739615 := by exact prefixLift 5739615
  have htrace : WordTrace (prefixWord ++ tailWord_5739615) baseStart_5739615 baseEnd_5739615 := by
    simpa [prefixWord, tailWord_5739615, baseEnd_5739615] using wordTrace_append hprefix tailTrace_5739615
  have hstable : (prefixWord ++ tailWord_5739615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739615).length < 2 ^ (prefixWord ++ tailWord_5739615).sum := by decide
  have hdescent : baseEnd_5739615 < baseStart_5739615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739628 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_5739628 : Nat := 118140960795 + 5739628 * 2 ^ 59
def prefixEnd_5739628 : Nat := 4983230072969 + 3 ^ 40 * 5739628 * 2
def baseEnd_5739628 : Nat := 2947187942004174912753937

theorem tailTrace_5739628 : CollatzResearch.WordTrace tailWord_5739628 prefixEnd_5739628 2947187942004174912753937 := by
  unfold tailWord_5739628
  simp only [CollatzResearch.WordTrace]
  refine ⟨104670715625157740632893769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139560954166876987510525025 104670715625157740632893769)
  ·
    refine ⟨78503036718868305474670327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104670715625157740632893769 78503036718868305474670327)
    ·
      refine ⟨117754555078302458212005491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78503036718868305474670327 117754555078302458212005491)
      ·
        refine ⟨176631832617453687318008237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117754555078302458212005491 176631832617453687318008237)
        ·
          refine ⟨66236937231545132744253089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176631832617453687318008237 66236937231545132744253089)
          ·
            refine ⟨49677702923658849558189817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66236937231545132744253089 49677702923658849558189817)
            ·
              refine ⟨37258277192744137168642363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49677702923658849558189817 37258277192744137168642363)
              ·
                refine ⟨55887415789116205752963545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37258277192744137168642363 55887415789116205752963545)
                ·
                  refine ⟨41915561841837154314722659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55887415789116205752963545 41915561841837154314722659)
                  ·
                    refine ⟨62873342762755731472083989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41915561841837154314722659 62873342762755731472083989)
                    ·
                      refine ⟨2947187942004174912753937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62873342762755731472083989 2947187942004174912753937)
                      ·
                        rfl

theorem cell23_5739628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_5739628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739628 prefixEnd_5739628 := by exact prefixLift 5739628
  have htrace : WordTrace (prefixWord ++ tailWord_5739628) baseStart_5739628 baseEnd_5739628 := by
    simpa [prefixWord, tailWord_5739628, baseEnd_5739628] using wordTrace_append hprefix tailTrace_5739628
  have hstable : (prefixWord ++ tailWord_5739628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739628).length < 2 ^ (prefixWord ++ tailWord_5739628).sum := by decide
  have hdescent : baseEnd_5739628 < baseStart_5739628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739699 : List Nat := [1, 1, 1, 2, 3, 2, 4, 4, 1, 1, 3]
def baseStart_5739699 : Nat := 118140960795 + 5739699 * 2 ^ 59
def prefixEnd_5739699 : Nat := 4983230072969 + 3 ^ 40 * 5739699 * 2
def baseEnd_5739699 : Nat := 2947224399130644134966111

theorem tailTrace_5739699 : CollatzResearch.WordTrace tailWord_5739699 prefixEnd_5739699 2947224399130644134966111 := by
  unfold tailWord_5739699
  simp only [CollatzResearch.WordTrace]
  refine ⟨209344020833058260391622151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139562680555372173594414767 209344020833058260391622151)
  ·
    refine ⟨314016031249587390587433227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209344020833058260391622151 314016031249587390587433227)
    ·
      refine ⟨471024046874381085881149841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314016031249587390587433227 471024046874381085881149841)
      ·
        refine ⟨353268035155785814410862381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471024046874381085881149841 353268035155785814410862381)
        ·
          refine ⟨132475513183419680404073393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353268035155785814410862381 132475513183419680404073393)
          ·
            refine ⟨99356634887564760303055045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132475513183419680404073393 99356634887564760303055045)
            ·
              refine ⟨18629369041418392556822821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99356634887564760303055045 18629369041418392556822821)
              ·
                refine ⟨3493006695265948604404279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18629369041418392556822821 3493006695265948604404279)
                ·
                  refine ⟨5239510042898922906606419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493006695265948604404279 5239510042898922906606419)
                  ·
                    refine ⟨7859265064348384359909629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5239510042898922906606419 7859265064348384359909629)
                    ·
                      refine ⟨2947224399130644134966111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7859265064348384359909629 2947224399130644134966111)
                      ·
                        rfl

theorem cell23_5739699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 1, 3].length) (baseStart_5739699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739699 prefixEnd_5739699 := by exact prefixLift 5739699
  have htrace : WordTrace (prefixWord ++ tailWord_5739699) baseStart_5739699 baseEnd_5739699 := by
    simpa [prefixWord, tailWord_5739699, baseEnd_5739699] using wordTrace_append hprefix tailTrace_5739699
  have hstable : (prefixWord ++ tailWord_5739699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739699).length < 2 ^ (prefixWord ++ tailWord_5739699).sum := by decide
  have hdescent : baseEnd_5739699 < baseStart_5739699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739722 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_5739722 : Nat := 118140960795 + 5739722 * 2 ^ 59
def prefixEnd_5739722 : Nat := 4983230072969 + 3 ^ 40 * 5739722 * 2
def baseEnd_5739722 : Nat := 2947236209185697544978505

theorem tailTrace_5739722 : CollatzResearch.WordTrace tailWord_5739722 prefixEnd_5739722 2947236209185697544978505 := by
  unfold tailWord_5739722
  simp only [CollatzResearch.WordTrace]
  refine ⟨52336214927993733829927355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139563239807983290213139613 52336214927993733829927355)
  ·
    refine ⟨78504322391990600744891033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52336214927993733829927355 78504322391990600744891033)
    ·
      refine ⟨58878241793992950558668275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78504322391990600744891033 58878241793992950558668275)
      ·
        refine ⟨88317362690989425838002413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58878241793992950558668275 88317362690989425838002413)
        ·
          refine ⟨33119011009121034689250905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88317362690989425838002413 33119011009121034689250905)
          ·
            refine ⟨24839258256840776016938179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33119011009121034689250905 24839258256840776016938179)
            ·
              refine ⟨37258887385261164025407269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24839258256840776016938179 37258887385261164025407269)
              ·
                refine ⟨6986041384736468254763863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37258887385261164025407269 6986041384736468254763863)
                ·
                  refine ⟨10479062077104702382145795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6986041384736468254763863 10479062077104702382145795)
                  ·
                    refine ⟨15718593115657053573218693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10479062077104702382145795 15718593115657053573218693)
                    ·
                      refine ⟨2947236209185697544978505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15718593115657053573218693 2947236209185697544978505)
                      ·
                        rfl

theorem cell23_5739722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_5739722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739722 prefixEnd_5739722 := by exact prefixLift 5739722
  have htrace : WordTrace (prefixWord ++ tailWord_5739722) baseStart_5739722 baseEnd_5739722 := by
    simpa [prefixWord, tailWord_5739722, baseEnd_5739722] using wordTrace_append hprefix tailTrace_5739722
  have hstable : (prefixWord ++ tailWord_5739722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739722).length < 2 ^ (prefixWord ++ tailWord_5739722).sum := by decide
  have hdescent : baseEnd_5739722 < baseStart_5739722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739733 : List Nat := [1, 3, 2, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5739733 : Nat := 118140960795 + 5739733 * 2 ^ 59
def prefixEnd_5739733 : Nat := 4983230072969 + 3 ^ 40 * 5739733 * 2
def baseEnd_5739733 : Nat := 2947241857472897001940955

theorem tailTrace_5739733 : CollatzResearch.WordTrace tailWord_5739733 prefixEnd_5739733 2947241857472897001940955 := by
  unfold tailWord_5739733
  simp only [CollatzResearch.WordTrace]
  refine ⟨209345260914935084198359853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139563507276623389465573235 209345260914935084198359853)
  ·
    refine ⟨78504472843100656574384945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209345260914935084198359853 78504472843100656574384945)
    ·
      refine ⟨58878354632325492430788709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78504472843100656574384945 58878354632325492430788709)
      ·
        refine ⟨11039691493561029830772883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58878354632325492430788709 11039691493561029830772883)
        ·
          refine ⟨16559537240341544746159325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11039691493561029830772883 16559537240341544746159325)
          ·
            refine ⟨6209826465128079279809747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16559537240341544746159325 6209826465128079279809747)
            ·
              refine ⟨9314739697692118919714621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209826465128079279809747 9314739697692118919714621)
              ·
                refine ⟨3493027386634544594892983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9314739697692118919714621 3493027386634544594892983)
                ·
                  refine ⟨5239541079951816892339475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493027386634544594892983 5239541079951816892339475)
                  ·
                    refine ⟨7859311619927725338509213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5239541079951816892339475 7859311619927725338509213)
                    ·
                      refine ⟨2947241857472897001940955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7859311619927725338509213 2947241857472897001940955)
                      ·
                        rfl

theorem cell23_5739733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5739733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739733 prefixEnd_5739733 := by exact prefixLift 5739733
  have htrace : WordTrace (prefixWord ++ tailWord_5739733) baseStart_5739733 baseEnd_5739733 := by
    simpa [prefixWord, tailWord_5739733, baseEnd_5739733] using wordTrace_append hprefix tailTrace_5739733
  have hstable : (prefixWord ++ tailWord_5739733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739733).length < 2 ^ (prefixWord ++ tailWord_5739733).sum := by decide
  have hdescent : baseEnd_5739733 < baseStart_5739733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739735 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_5739735 : Nat := 118140960795 + 5739735 * 2 ^ 59
def prefixEnd_5739735 : Nat := 4983230072969 + 3 ^ 40 * 5739735 * 2
def baseEnd_5739735 : Nat := 2947242884434205994115945

theorem tailTrace_5739735 : CollatzResearch.WordTrace tailWord_5739735 prefixEnd_5739735 2947242884434205994115945 := by
  unfold tailWord_5739735
  simp only [CollatzResearch.WordTrace]
  refine ⟨209345333860927838539932659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139563555907285225693288439 209345333860927838539932659)
  ·
    refine ⟨314018000791391757809898989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209345333860927838539932659 314018000791391757809898989)
    ·
      refine ⟨117756750296771909178712121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314018000791391757809898989 117756750296771909178712121)
      ·
        refine ⟨88317562722578931884034091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117756750296771909178712121 88317562722578931884034091)
        ·
          refine ⟨132476344083868397826051137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88317562722578931884034091 132476344083868397826051137)
          ·
            refine ⟨99357258062901298369538353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132476344083868397826051137 99357258062901298369538353)
            ·
              refine ⟨74517943547175973777153765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99357258062901298369538353 74517943547175973777153765)
              ·
                refine ⟨13972114415095495083216331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74517943547175973777153765 13972114415095495083216331)
                ·
                  refine ⟨20958171622643242624824497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13972114415095495083216331 20958171622643242624824497)
                  ·
                    refine ⟨15718628716982431968618373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20958171622643242624824497 15718628716982431968618373)
                    ·
                      refine ⟨2947242884434205994115945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15718628716982431968618373 2947242884434205994115945)
                      ·
                        rfl

theorem cell23_5739735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_5739735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739735 prefixEnd_5739735 := by exact prefixLift 5739735
  have htrace : WordTrace (prefixWord ++ tailWord_5739735) baseStart_5739735 baseEnd_5739735 := by
    simpa [prefixWord, tailWord_5739735, baseEnd_5739735] using wordTrace_append hprefix tailTrace_5739735
  have hstable : (prefixWord ++ tailWord_5739735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739735).length < 2 ^ (prefixWord ++ tailWord_5739735).sum := by decide
  have hdescent : baseEnd_5739735 < baseStart_5739735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739745 : List Nat := [1, 2, 3, 1, 3, 4, 9]
def baseStart_5739745 : Nat := 118140960795 + 5739745 * 2 ^ 59
def prefixEnd_5739745 : Nat := 4983230072969 + 3 ^ 40 * 5739745 * 2
def baseEnd_5739745 : Nat := 36385778015317913024579

theorem tailTrace_5739745 : CollatzResearch.WordTrace tailWord_5739745 prefixEnd_5739745 36385778015317913024579 := by
  unfold tailWord_5739745
  simp only [CollatzResearch.WordTrace]
  refine ⟨209345698590891610247796689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139563799060594406831864459 209345698590891610247796689)
  ·
    refine ⟨157009273943168707685847517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209345698590891610247796689 157009273943168707685847517)
    ·
      refine ⟨58878477728688265382192819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157009273943168707685847517 58878477728688265382192819)
      ·
        refine ⟨88317716593032398073289229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58878477728688265382192819 88317716593032398073289229)
        ·
          refine ⟨33119143722387149277483461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88317716593032398073289229 33119143722387149277483461)
          ·
            refine ⟨6209839447947590489528149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33119143722387149277483461 6209839447947590489528149)
            ·
              refine ⟨36385778015317913024579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6209839447947590489528149 36385778015317913024579)
              ·
                rfl

theorem cell23_5739745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 9].length) (baseStart_5739745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739745 prefixEnd_5739745 := by exact prefixLift 5739745
  have htrace : WordTrace (prefixWord ++ tailWord_5739745) baseStart_5739745 baseEnd_5739745 := by
    simpa [prefixWord, tailWord_5739745, baseEnd_5739745] using wordTrace_append hprefix tailTrace_5739745
  have hstable : (prefixWord ++ tailWord_5739745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739745).length < 2 ^ (prefixWord ++ tailWord_5739745).sum := by decide
  have hdescent : baseEnd_5739745 < baseStart_5739745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739756 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 3, 2, 2]
def baseStart_5739756 : Nat := 118140960795 + 5739756 * 2 ^ 59
def prefixEnd_5739756 : Nat := 4983230072969 + 3 ^ 40 * 5739756 * 2
def baseEnd_5739756 : Nat := 2947253667527950411953349

theorem tailTrace_5739756 : CollatzResearch.WordTrace tailWord_5739756 prefixEnd_5739756 2947253667527950411953349 := by
  unfold tailWord_5739756
  simp only [CollatzResearch.WordTrace]
  refine ⟨104673049896925879563223561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139564066529234506084298081 104673049896925879563223561)
  ·
    refine ⟨78504787422694409672417671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104673049896925879563223561 78504787422694409672417671)
    ·
      refine ⟨117757181134041614508626507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78504787422694409672417671 117757181134041614508626507)
      ·
        refine ⟨176635771701062421762939761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117757181134041614508626507 176635771701062421762939761)
        ·
          refine ⟨132476828775796816322204821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176635771701062421762939761 132476828775796816322204821)
          ·
            refine ⟨6209851348865475765103351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132476828775796816322204821 6209851348865475765103351)
            ·
              refine ⟨9314777023298213647655027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209851348865475765103351 9314777023298213647655027)
              ·
                refine ⟨13972165534947320471482541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9314777023298213647655027 13972165534947320471482541)
                ·
                  refine ⟨5239562075605245176805953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13972165534947320471482541 5239562075605245176805953)
                  ·
                    refine ⟨3929671556703933882604465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239562075605245176805953 3929671556703933882604465)
                    ·
                      refine ⟨2947253667527950411953349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929671556703933882604465 2947253667527950411953349)
                      ·
                        rfl

theorem cell23_5739756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_5739756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739756 prefixEnd_5739756 := by exact prefixLift 5739756
  have htrace : WordTrace (prefixWord ++ tailWord_5739756) baseStart_5739756 baseEnd_5739756 := by
    simpa [prefixWord, tailWord_5739756, baseEnd_5739756] using wordTrace_append hprefix tailTrace_5739756
  have hstable : (prefixWord ++ tailWord_5739756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739756).length < 2 ^ (prefixWord ++ tailWord_5739756).sum := by decide
  have hdescent : baseEnd_5739756 < baseStart_5739756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739762 : List Nat := [3, 2, 1, 3, 3, 1, 2, 8]
def baseStart_5739762 : Nat := 118140960795 + 5739762 * 2 ^ 59
def prefixEnd_5739762 : Nat := 4983230072969 + 3 ^ 40 * 5739762 * 2
def baseEnd_5739762 : Nat := 109157657348588051425123

theorem tailTrace_5739762 : CollatzResearch.WordTrace tailWord_5739762 prefixEnd_5739762 109157657348588051425123 := by
  unfold tailWord_5739762
  simp only [CollatzResearch.WordTrace]
  refine ⟨52336579657957505537791385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139564212421220014767443693 52336579657957505537791385)
  ·
    refine ⟨39252434743468129153343539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52336579657957505537791385 39252434743468129153343539)
    ·
      refine ⟨58878652115202193730015309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39252434743468129153343539 58878652115202193730015309)
      ·
        refine ⟨22079494543200822648755741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58878652115202193730015309 22079494543200822648755741)
        ·
          refine ⟨8279810453700308493283403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22079494543200822648755741 8279810453700308493283403)
          ·
            refine ⟨12419715680550462739925105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8279810453700308493283403 12419715680550462739925105)
            ·
              refine ⟨9314786760412847054943829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12419715680550462739925105 9314786760412847054943829)
              ·
                refine ⟨109157657348588051425123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9314786760412847054943829 109157657348588051425123)
                ·
                  rfl

theorem cell23_5739762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 8].length) (baseStart_5739762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739762 prefixEnd_5739762 := by exact prefixLift 5739762
  have htrace : WordTrace (prefixWord ++ tailWord_5739762) baseStart_5739762 baseEnd_5739762 := by
    simpa [prefixWord, tailWord_5739762, baseEnd_5739762] using wordTrace_append hprefix tailTrace_5739762
  have hstable : (prefixWord ++ tailWord_5739762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739762).length < 2 ^ (prefixWord ++ tailWord_5739762).sum := by decide
  have hdescent : baseEnd_5739762 < baseStart_5739762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739807 : List Nat := [1, 1, 2, 4, 5, 1, 2, 2, 1, 2, 2]
def baseStart_5739807 : Nat := 118140960795 + 5739807 * 2 ^ 59
def prefixEnd_5739807 : Nat := 4983230072969 + 3 ^ 40 * 5739807 * 2
def baseEnd_5739807 : Nat := 2947279855041329712415615

theorem tailTrace_5739807 : CollatzResearch.WordTrace tailWord_5739807 prefixEnd_5739807 2947279855041329712415615 := by
  unfold tailWord_5739807
  simp only [CollatzResearch.WordTrace]
  refine ⟨209347959916666994836553675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139565306611111329891035783 209347959916666994836553675)
  ·
    refine ⟨314021939875000492254830513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209347959916666994836553675 314021939875000492254830513)
    ·
      refine ⟨235516454906250369191122885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314021939875000492254830513 235516454906250369191122885)
      ·
        refine ⟨44159335294921944223335541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235516454906250369191122885 44159335294921944223335541)
        ·
          refine ⟨4139937683898932270937707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44159335294921944223335541 4139937683898932270937707)
          ·
            refine ⟨6209906525848398406406561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139937683898932270937707 6209906525848398406406561)
            ·
              refine ⟨4657429894386298804804921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6209906525848398406406561 4657429894386298804804921)
              ·
                refine ⟨3493072420789724103603691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657429894386298804804921 3493072420789724103603691)
                ·
                  refine ⟨5239608631184586155405537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493072420789724103603691 5239608631184586155405537)
                  ·
                    refine ⟨3929706473388439616554153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239608631184586155405537 3929706473388439616554153)
                    ·
                      refine ⟨2947279855041329712415615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929706473388439616554153 2947279855041329712415615)
                      ·
                        rfl

theorem cell23_5739807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_5739807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739807 prefixEnd_5739807 := by exact prefixLift 5739807
  have htrace : WordTrace (prefixWord ++ tailWord_5739807) baseStart_5739807 baseEnd_5739807 := by
    simpa [prefixWord, tailWord_5739807, baseEnd_5739807] using wordTrace_append hprefix tailTrace_5739807
  have hstable : (prefixWord ++ tailWord_5739807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739807).length < 2 ^ (prefixWord ++ tailWord_5739807).sum := by decide
  have hdescent : baseEnd_5739807 < baseStart_5739807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739829 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_5739829 : Nat := 118140960795 + 5739829 * 2 ^ 59
def prefixEnd_5739829 : Nat := 4983230072969 + 3 ^ 40 * 5739829 * 2
def baseEnd_5739829 : Nat := 2947291151615728626340513

theorem tailTrace_5739829 : CollatzResearch.WordTrace tailWord_5739829 prefixEnd_5739829 2947291151615728626340513 := by
  unfold tailWord_5739829
  simp only [CollatzResearch.WordTrace]
  refine ⟨209348762322587292593854541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139565841548391528395903027 209348762322587292593854541)
  ·
    refine ⟨78505785870970234722695453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209348762322587292593854541 78505785870970234722695453)
    ·
      refine ⟨29439669701613838021010795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78505785870970234722695453 29439669701613838021010795)
      ·
        refine ⟨44159504552420757031516193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29439669701613838021010795 44159504552420757031516193)
        ·
          refine ⟨33119628414315567773637145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44159504552420757031516193 33119628414315567773637145)
          ·
            refine ⟨24839721310736675830227859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33119628414315567773637145 24839721310736675830227859)
            ·
              refine ⟨37259581966105013745341789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24839721310736675830227859 37259581966105013745341789)
              ·
                refine ⟨13972343237289380154503171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37259581966105013745341789 13972343237289380154503171)
                ·
                  refine ⟨20958514855934070231754757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13972343237289380154503171 20958514855934070231754757)
                  ·
                    refine ⟨3929721535487638168454017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20958514855934070231754757 3929721535487638168454017)
                    ·
                      refine ⟨2947291151615728626340513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929721535487638168454017 2947291151615728626340513)
                      ·
                        rfl

theorem cell23_5739829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_5739829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739829 prefixEnd_5739829 := by exact prefixLift 5739829
  have htrace : WordTrace (prefixWord ++ tailWord_5739829) baseStart_5739829 baseEnd_5739829 := by
    simpa [prefixWord, tailWord_5739829, baseEnd_5739829] using wordTrace_append hprefix tailTrace_5739829
  have hstable : (prefixWord ++ tailWord_5739829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739829).length < 2 ^ (prefixWord ++ tailWord_5739829).sum := by decide
  have hdescent : baseEnd_5739829 < baseStart_5739829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739863 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 2, 2, 2]
def baseStart_5739863 : Nat := 118140960795 + 5739863 * 2 ^ 59
def prefixEnd_5739863 : Nat := 4983230072969 + 3 ^ 40 * 5739863 * 2
def baseEnd_5739863 : Nat := 2947308609957981493315357

theorem tailTrace_5739863 : CollatzResearch.WordTrace tailWord_5739863 prefixEnd_5739863 2947308609957981493315357 := by
  unfold tailWord_5739863
  simp only [CollatzResearch.WordTrace]
  refine ⟨209350002404464116400592243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139566668269642744267061495 209350002404464116400592243)
  ·
    refine ⟨314025003606696174600888365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209350002404464116400592243 314025003606696174600888365)
    ·
      refine ⟨117759376352511065475333137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314025003606696174600888365 117759376352511065475333137)
      ·
        refine ⟨88319532264383299106499853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117759376352511065475333137 88319532264383299106499853)
        ·
          refine ⟨33119824599143737164937445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88319532264383299106499853 33119824599143737164937445)
          ·
            refine ⟨6209967112339450718425771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33119824599143737164937445 6209967112339450718425771)
            ·
              refine ⟨9314950668509176077638657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6209967112339450718425771 9314950668509176077638657)
              ·
                refine ⟨6986213001381882058228993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9314950668509176077638657 6986213001381882058228993)
                ·
                  refine ⟨5239659751036411543671745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6986213001381882058228993 5239659751036411543671745)
                  ·
                    refine ⟨3929744813277308657753809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239659751036411543671745 3929744813277308657753809)
                    ·
                      refine ⟨2947308609957981493315357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929744813277308657753809 2947308609957981493315357)
                      ·
                        rfl

theorem cell23_5739863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_5739863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739863 prefixEnd_5739863 := by exact prefixLift 5739863
  have htrace : WordTrace (prefixWord ++ tailWord_5739863) baseStart_5739863 baseEnd_5739863 := by
    simpa [prefixWord, tailWord_5739863, baseEnd_5739863] using wordTrace_append hprefix tailTrace_5739863
  have hstable : (prefixWord ++ tailWord_5739863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739863).length < 2 ^ (prefixWord ++ tailWord_5739863).sum := by decide
  have hdescent : baseEnd_5739863 < baseStart_5739863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739880 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5739880 : Nat := 118140960795 + 5739880 * 2 ^ 59
def prefixEnd_5739880 : Nat := 4983230072969 + 3 ^ 40 * 5739880 * 2
def baseEnd_5739880 : Nat := 2947317339129107926802779

theorem tailTrace_5739880 : CollatzResearch.WordTrace tailWord_5739880 prefixEnd_5739880 2947317339129107926802779 := by
  unfold tailWord_5739880
  simp only [CollatzResearch.WordTrace]
  refine ⟨104675311222701264151980547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139567081630268352202640729 104675311222701264151980547)
  ·
    refine ⟨157012966834051896227970821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104675311222701264151980547 157012966834051896227970821)
    ·
      refine ⟨29439931281384730542744529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157012966834051896227970821 29439931281384730542744529)
      ·
        refine ⟨22079948461038547907058397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29439931281384730542744529 22079948461038547907058397)
        ·
          refine ⟨8279980672889455465146899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22079948461038547907058397 8279980672889455465146899)
          ·
            refine ⟨12419971009334183197720349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8279980672889455465146899 12419971009334183197720349)
            ·
              refine ⟨4657489128500318699145131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12419971009334183197720349 4657489128500318699145131)
              ·
                refine ⟨6986233692750478048717697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657489128500318699145131 6986233692750478048717697)
                ·
                  refine ⟨5239675269562858536538273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6986233692750478048717697 5239675269562858536538273)
                  ·
                    refine ⟨3929756452172143902403705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239675269562858536538273 3929756452172143902403705)
                    ·
                      refine ⟨2947317339129107926802779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929756452172143902403705 2947317339129107926802779)
                      ·
                        rfl

theorem cell23_5739880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5739880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739880 prefixEnd_5739880 := by exact prefixLift 5739880
  have htrace : WordTrace (prefixWord ++ tailWord_5739880) baseStart_5739880 baseEnd_5739880 := by
    simpa [prefixWord, tailWord_5739880, baseEnd_5739880] using wordTrace_append hprefix tailTrace_5739880
  have hstable : (prefixWord ++ tailWord_5739880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739880).length < 2 ^ (prefixWord ++ tailWord_5739880).sum := by decide
  have hdescent : baseEnd_5739880 < baseStart_5739880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739895 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 2, 8]
def baseStart_5739895 : Nat := 118140960795 + 5739895 * 2 ^ 59
def prefixEnd_5739895 : Nat := 4983230072969 + 3 ^ 40 * 5739895 * 2
def baseEnd_5739895 : Nat := 982441680446308456038403

theorem tailTrace_5739895 : CollatzResearch.WordTrace tailWord_5739895 prefixEnd_5739895 982441680446308456038403 := by
  unfold tailWord_5739895
  simp only [CollatzResearch.WordTrace]
  refine ⟨209351169540348185865757139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139567446360232123910504759 209351169540348185865757139)
  ·
    refine ⟨314026754310522278798635709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209351169540348185865757139 314026754310522278798635709)
    ·
      refine ⟨117760032866445854549488391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314026754310522278798635709 117760032866445854549488391)
      ·
        refine ⟨176640049299668781824232587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117760032866445854549488391 176640049299668781824232587)
        ·
          refine ⟨264960073949503172736348881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176640049299668781824232587 264960073949503172736348881)
          ·
            refine ⟨198720055462127379552261661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264960073949503172736348881 198720055462127379552261661)
            ·
              refine ⟨74520020798297767332098123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198720055462127379552261661 74520020798297767332098123)
              ·
                refine ⟨111780031197446650998147185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74520020798297767332098123 111780031197446650998147185)
                ·
                  refine ⟨83835023398084988248610389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111780031197446650998147185 83835023398084988248610389)
                  ·
                    refine ⟨982441680446308456038403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83835023398084988248610389 982441680446308456038403)
                    ·
                      rfl

theorem cell23_5739895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_5739895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739895 prefixEnd_5739895 := by exact prefixLift 5739895
  have htrace : WordTrace (prefixWord ++ tailWord_5739895) baseStart_5739895 baseEnd_5739895 := by
    simpa [prefixWord, tailWord_5739895, baseEnd_5739895] using wordTrace_append hprefix tailTrace_5739895
  have hstable : (prefixWord ++ tailWord_5739895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739895).length < 2 ^ (prefixWord ++ tailWord_5739895).sum := by decide
  have hdescent : baseEnd_5739895 < baseStart_5739895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739929 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 3, 4]
def baseStart_5739929 : Nat := 118140960795 + 5739929 * 2 ^ 59
def prefixEnd_5739929 : Nat := 4983230072969 + 3 ^ 40 * 5739929 * 2
def baseEnd_5739929 : Nat := 982447499893726078363351

theorem tailTrace_5739929 : CollatzResearch.WordTrace tailWord_5739929 prefixEnd_5739929 982447499893726078363351 := by
  unfold tailWord_5739929
  simp only [CollatzResearch.WordTrace]
  refine ⟨209352409622225009672494841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139568273081483339781663227 209352409622225009672494841)
  ·
    refine ⟨157014307216668757254371131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209352409622225009672494841 157014307216668757254371131)
    ·
      refine ⟨235521460825003135881556697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157014307216668757254371131 235521460825003135881556697)
      ·
        refine ⟨176641095618752351911167523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235521460825003135881556697 176641095618752351911167523)
        ·
          refine ⟨264961643428128527866751285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176641095618752351911167523 264961643428128527866751285)
          ·
            refine ⟨24840154071387049487507933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264961643428128527866751285 24840154071387049487507933)
            ·
              refine ⟨9315057776770143557815475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24840154071387049487507933 9315057776770143557815475)
              ·
                refine ⟨13972586665155215336723213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9315057776770143557815475 13972586665155215336723213)
                ·
                  refine ⟨5239719999433205751271205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13972586665155215336723213 5239719999433205751271205)
                  ·
                    refine ⟨982447499893726078363351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5239719999433205751271205 982447499893726078363351)
                    ·
                      rfl

theorem cell23_5739929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_5739929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739929 prefixEnd_5739929 := by exact prefixLift 5739929
  have htrace : WordTrace (prefixWord ++ tailWord_5739929) baseStart_5739929 baseEnd_5739929 := by
    simpa [prefixWord, tailWord_5739929, baseEnd_5739929] using wordTrace_append hprefix tailTrace_5739929
  have hstable : (prefixWord ++ tailWord_5739929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739929).length < 2 ^ (prefixWord ++ tailWord_5739929).sum := by decide
  have hdescent : baseEnd_5739929 < baseStart_5739929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5739980 : List Nat := [2, 2, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_5739980 : Nat := 118140960795 + 5739980 * 2 ^ 59
def prefixEnd_5739980 : Nat := 4983230072969 + 3 ^ 40 * 5739980 * 2
def baseEnd_5739980 : Nat := 982456229064852511850773

theorem tailTrace_5739980 : CollatzResearch.WordTrace tailWord_5739980 prefixEnd_5739980 982456229064852511850773 := by
  unfold tailWord_5739980
  simp only [CollatzResearch.WordTrace]
  refine ⟨104677134872520122691300697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139569513163360163588400929 104677134872520122691300697)
  ·
    refine ⟨78507851154390092018475523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104677134872520122691300697 78507851154390092018475523)
    ·
      refine ⟨117761776731585138027713285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78507851154390092018475523 117761776731585138027713285)
      ·
        refine ⟨22080333137172213380196241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117761776731585138027713285 22080333137172213380196241)
        ·
          refine ⟨16560249852879160035147181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22080333137172213380196241 16560249852879160035147181)
          ·
            refine ⟨6210093694829685013180193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16560249852879160035147181 6210093694829685013180193)
            ·
              refine ⟨4657570271122263759885145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6210093694829685013180193 4657570271122263759885145)
              ·
                refine ⟨3493177703341697819913859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657570271122263759885145 3493177703341697819913859)
                ·
                  refine ⟨5239766555012546729870789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493177703341697819913859 5239766555012546729870789)
                  ·
                    refine ⟨982456229064852511850773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5239766555012546729870789 982456229064852511850773)
                    ·
                      rfl

theorem cell23_5739980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_5739980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5739980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5739980 prefixEnd_5739980 := by exact prefixLift 5739980
  have htrace : WordTrace (prefixWord ++ tailWord_5739980) baseStart_5739980 baseEnd_5739980 := by
    simpa [prefixWord, tailWord_5739980, baseEnd_5739980] using wordTrace_append hprefix tailTrace_5739980
  have hstable : (prefixWord ++ tailWord_5739980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5739980).length < 2 ^ (prefixWord ++ tailWord_5739980).sum := by decide
  have hdescent : baseEnd_5739980 < baseStart_5739980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5739980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740012 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_5740012 : Nat := 118140960795 + 5740012 * 2 ^ 59
def prefixEnd_5740012 : Nat := 4983230072969 + 3 ^ 40 * 5740012 * 2
def baseEnd_5740012 : Nat := 2947385118575501410352171

theorem tailTrace_5740012 : CollatzResearch.WordTrace tailWord_5740012 prefixEnd_5740012 2947385118575501410352171 := by
  unfold tailWord_5740012
  simp only [CollatzResearch.WordTrace]
  refine ⟨104677718440462157423883145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139570291253949543231844193 104677718440462157423883145)
  ·
    refine ⟨78508288830346618067912359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104677718440462157423883145 78508288830346618067912359)
    ·
      refine ⟨117762433245519927101868539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78508288830346618067912359 117762433245519927101868539)
      ·
        refine ⟨176643649868279890652802809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117762433245519927101868539 176643649868279890652802809)
        ·
          refine ⟨132482737401209917989602107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176643649868279890652802809 132482737401209917989602107)
          ·
            refine ⟨198724106101814876984403161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132482737401209917989602107 198724106101814876984403161)
            ·
              refine ⟨149043079576361157738302371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198724106101814876984403161 149043079576361157738302371)
              ·
                refine ⟨223564619364541736607453557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149043079576361157738302371 223564619364541736607453557)
                ·
                  refine ⟨20959183065425787806948771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223564619364541736607453557 20959183065425787806948771)
                  ·
                    refine ⟨31438774598138681710423157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20959183065425787806948771 31438774598138681710423157)
                    ·
                      refine ⟨2947385118575501410352171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31438774598138681710423157 2947385118575501410352171)
                      ·
                        rfl

theorem cell23_5740012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_5740012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740012 prefixEnd_5740012 := by exact prefixLift 5740012
  have htrace : WordTrace (prefixWord ++ tailWord_5740012) baseStart_5740012 baseEnd_5740012 := by
    simpa [prefixWord, tailWord_5740012, baseEnd_5740012] using wordTrace_append hprefix tailTrace_5740012
  have hstable : (prefixWord ++ tailWord_5740012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740012).length < 2 ^ (prefixWord ++ tailWord_5740012).sum := by decide
  have hdescent : baseEnd_5740012 < baseStart_5740012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740013 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5740013 : Nat := 118140960795 + 5740013 * 2 ^ 59
def prefixEnd_5740013 : Nat := 4983230072969 + 3 ^ 40 * 5740013 * 2
def baseEnd_5740013 : Nat := 2947385632056155906439667

theorem tailTrace_5740013 : CollatzResearch.WordTrace tailWord_5740013 prefixEnd_5740013 2947385632056155906439667 := by
  unfold tailWord_5740013
  simp only [CollatzResearch.WordTrace]
  refine ⟨209355473353920692018552693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139570315569280461345701795 209355473353920692018552693)
  ·
    refine ⟨19627075626930064876739315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209355473353920692018552693 19627075626930064876739315)
    ·
      refine ⟨29440613440395097315108973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19627075626930064876739315 29440613440395097315108973)
      ·
        refine ⟨11040230040148161493165865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29440613440395097315108973 11040230040148161493165865)
        ·
          refine ⟨8280172530111121119874399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11040230040148161493165865 8280172530111121119874399)
          ·
            refine ⟨12420258795166681679811599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8280172530111121119874399 12420258795166681679811599)
            ·
              refine ⟨18630388192750022519717399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12420258795166681679811599 18630388192750022519717399)
              ·
                refine ⟨27945582289125033779576099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18630388192750022519717399 27945582289125033779576099)
                ·
                  refine ⟨41918373433687550669364149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27945582289125033779576099 41918373433687550669364149)
                  ·
                    refine ⟨3929847509408207875252889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41918373433687550669364149 3929847509408207875252889)
                    ·
                      refine ⟨2947385632056155906439667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929847509408207875252889 2947385632056155906439667)
                      ·
                        rfl

theorem cell23_5740013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5740013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740013 prefixEnd_5740013 := by exact prefixLift 5740013
  have htrace : WordTrace (prefixWord ++ tailWord_5740013) baseStart_5740013 baseEnd_5740013 := by
    simpa [prefixWord, tailWord_5740013, baseEnd_5740013] using wordTrace_append hprefix tailTrace_5740013
  have hstable : (prefixWord ++ tailWord_5740013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740013).length < 2 ^ (prefixWord ++ tailWord_5740013).sum := by decide
  have hdescent : baseEnd_5740013 < baseStart_5740013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740026 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2]
def baseStart_5740026 : Nat := 118140960795 + 5740026 * 2 ^ 59
def prefixEnd_5740026 : Nat := 4983230072969 + 3 ^ 40 * 5740026 * 2
def baseEnd_5740026 : Nat := 2947392307304664355577107

theorem tailTrace_5740026 : CollatzResearch.WordTrace tailWord_5740026 prefixEnd_5740026 2947392307304664355577107 := by
  unfold tailWord_5740026
  simp only [CollatzResearch.WordTrace]
  refine ⟨52338986875718398809693983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139570631668582396825850621 52338986875718398809693983)
  ·
    refine ⟨78508480313577598214540975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52338986875718398809693983 78508480313577598214540975)
    ·
      refine ⟨117762720470366397321811463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78508480313577598214540975 117762720470366397321811463)
      ·
        refine ⟨176644080705549595982717195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117762720470366397321811463 176644080705549595982717195)
        ·
          refine ⟨264966121058324393974075793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176644080705549595982717195 264966121058324393974075793)
          ·
            refine ⟨198724590793743295480556845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264966121058324393974075793 198724590793743295480556845)
            ·
              refine ⟨74521721547653735805208817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198724590793743295480556845 74521721547653735805208817)
              ·
                refine ⟨55891291160740301853906613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74521721547653735805208817 55891291160740301853906613)
                ·
                  refine ⟨5239808546319403298803745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55891291160740301853906613 5239808546319403298803745)
                  ·
                    refine ⟨3929856409739552474102809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5239808546319403298803745 3929856409739552474102809)
                    ·
                      refine ⟨2947392307304664355577107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929856409739552474102809 2947392307304664355577107)
                      ·
                        rfl

theorem cell23_5740026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_5740026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740026 prefixEnd_5740026 := by exact prefixLift 5740026
  have htrace : WordTrace (prefixWord ++ tailWord_5740026) baseStart_5740026 baseEnd_5740026 := by
    simpa [prefixWord, tailWord_5740026, baseEnd_5740026] using wordTrace_append hprefix tailTrace_5740026
  have hstable : (prefixWord ++ tailWord_5740026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740026).length < 2 ^ (prefixWord ++ tailWord_5740026).sum := by decide
  have hdescent : baseEnd_5740026 < baseStart_5740026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740046 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_5740046 : Nat := 118140960795 + 5740046 * 2 ^ 59
def prefixEnd_5740046 : Nat := 4983230072969 + 3 ^ 40 * 5740046 * 2
def baseEnd_5740046 : Nat := 2947402576917754277327015

theorem tailTrace_5740046 : CollatzResearch.WordTrace tailWord_5740046 prefixEnd_5740046 2947402576917754277327015 := by
  unfold tailWord_5740046
  simp only [CollatzResearch.WordTrace]
  refine ⟨26169584620350142331812999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139571117975200759103002661 26169584620350142331812999)
  ·
    refine ⟨39254376930525213497719499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26169584620350142331812999 39254376930525213497719499)
    ·
      refine ⟨58881565395787820246579249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39254376930525213497719499 58881565395787820246579249)
      ·
        refine ⟨44161174046840865184934437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58881565395787820246579249 44161174046840865184934437)
        ·
          refine ⟨8280220133782662222175207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44161174046840865184934437 8280220133782662222175207)
          ·
            refine ⟨12420330200673993333262811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8280220133782662222175207 12420330200673993333262811)
            ·
              refine ⟨18630495301010989999894217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12420330200673993333262811 18630495301010989999894217)
              ·
                refine ⟨13972871475758242499920663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18630495301010989999894217 13972871475758242499920663)
                ·
                  refine ⟨20959307213637363749880995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13972871475758242499920663 20959307213637363749880995)
                  ·
                    refine ⟨31438960820456045624821493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20959307213637363749880995 31438960820456045624821493)
                    ·
                      refine ⟨2947402576917754277327015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31438960820456045624821493 2947402576917754277327015)
                      ·
                        rfl

theorem cell23_5740046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_5740046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740046 prefixEnd_5740046 := by exact prefixLift 5740046
  have htrace : WordTrace (prefixWord ++ tailWord_5740046) baseStart_5740046 baseEnd_5740046 := by
    simpa [prefixWord, tailWord_5740046, baseEnd_5740046] using wordTrace_append hprefix tailTrace_5740046
  have hstable : (prefixWord ++ tailWord_5740046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740046).length < 2 ^ (prefixWord ++ tailWord_5740046).sum := by decide
  have hdescent : baseEnd_5740046 < baseStart_5740046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740053 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_5740053 : Nat := 118140960795 + 5740053 * 2 ^ 59
def prefixEnd_5740053 : Nat := 4983230072969 + 3 ^ 40 * 5740053 * 2
def baseEnd_5740053 : Nat := 982468723760778583313161

theorem tailTrace_5740053 : CollatzResearch.WordTrace tailWord_5740053 prefixEnd_5740053 982468723760778583313161 := by
  unfold tailWord_5740053
  simp only [CollatzResearch.WordTrace]
  refine ⟨209356932273775778850008813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139571288182517185900005875 209356932273775778850008813)
  ·
    refine ⟨78508849602665917068753305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209356932273775778850008813 78508849602665917068753305)
    ·
      refine ⟨58881637201999437801564979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78508849602665917068753305 58881637201999437801564979)
      ·
        refine ⟨88322455802999156702347469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58881637201999437801564979 88322455802999156702347469)
        ·
          refine ⟨33120920926124683763380301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88322455802999156702347469 33120920926124683763380301)
          ·
            refine ⟨12420345347296756411267613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33120920926124683763380301 12420345347296756411267613)
            ·
              refine ⟨4657629505236283654225355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12420345347296756411267613 4657629505236283654225355)
              ·
                refine ⟨6986444257854425481338033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657629505236283654225355 6986444257854425481338033)
                ·
                  refine ⟨5239833193390819111003525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6986444257854425481338033 5239833193390819111003525)
                  ·
                    refine ⟨982468723760778583313161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5239833193390819111003525 982468723760778583313161)
                    ·
                      rfl

theorem cell23_5740053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_5740053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740053 prefixEnd_5740053 := by exact prefixLift 5740053
  have htrace : WordTrace (prefixWord ++ tailWord_5740053) baseStart_5740053 baseEnd_5740053 := by
    simpa [prefixWord, tailWord_5740053, baseEnd_5740053] using wordTrace_append hprefix tailTrace_5740053
  have hstable : (prefixWord ++ tailWord_5740053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740053).length < 2 ^ (prefixWord ++ tailWord_5740053).sum := by decide
  have hdescent : baseEnd_5740053 < baseStart_5740053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740119 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_5740119 : Nat := 118140960795 + 5740119 * 2 ^ 59
def prefixEnd_5740119 : Nat := 4983230072969 + 3 ^ 40 * 5740119 * 2
def baseEnd_5740119 : Nat := 2947440061005532491714179

theorem tailTrace_5740119 : CollatzResearch.WordTrace tailWord_5740119 prefixEnd_5740119 2947440061005532491714179 := by
  unfold tailWord_5740119
  simp only [CollatzResearch.WordTrace]
  refine ⟨209359339491536672121911411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139572892994357781414607607 209359339491536672121911411)
  ·
    refine ⟨314039009237305008182867117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209359339491536672121911411 314039009237305008182867117)
    ·
      refine ⟨117764628463989378068575169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314039009237305008182867117 117764628463989378068575169)
      ·
        refine ⟨88323471347992033551431377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117764628463989378068575169 88323471347992033551431377)
        ·
          refine ⟨66242603510994025163573533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88323471347992033551431377 66242603510994025163573533)
          ·
            refine ⟨24840976316622759436340075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66242603510994025163573533 24840976316622759436340075)
            ·
              refine ⟨37261464474934139154510113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24840976316622759436340075 37261464474934139154510113)
              ·
                refine ⟨27946098356200604365882585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37261464474934139154510113 27946098356200604365882585)
                ·
                  refine ⟨20959573767150453274411939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27946098356200604365882585 20959573767150453274411939)
                  ·
                    refine ⟨31439360650725679911617909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20959573767150453274411939 31439360650725679911617909)
                    ·
                      refine ⟨2947440061005532491714179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31439360650725679911617909 2947440061005532491714179)
                      ·
                        rfl

theorem cell23_5740119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_5740119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740119 prefixEnd_5740119 := by exact prefixLift 5740119
  have htrace : WordTrace (prefixWord ++ tailWord_5740119) baseStart_5740119 baseEnd_5740119 := by
    simpa [prefixWord, tailWord_5740119, baseEnd_5740119] using wordTrace_append hprefix tailTrace_5740119
  have hstable : (prefixWord ++ tailWord_5740119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740119).length < 2 ^ (prefixWord ++ tailWord_5740119).sum := by decide
  have hdescent : baseEnd_5740119 < baseStart_5740119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740133 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 1, 4, 2]
def baseStart_5740133 : Nat := 118140960795 + 5740133 * 2 ^ 59
def prefixEnd_5740133 : Nat := 4983230072969 + 3 ^ 40 * 5740133 * 2
def baseEnd_5740133 : Nat := 2947447249734695436939115

theorem tailTrace_5740133 : CollatzResearch.WordTrace tailWord_5740133 prefixEnd_5740133 2947447249734695436939115 := by
  unfold tailWord_5740133
  simp only [CollatzResearch.WordTrace]
  refine ⟨209359850113485952512921053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139573233408990635008614035 209359850113485952512921053)
  ·
    refine ⟨78509943792557232192345395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209359850113485952512921053 78509943792557232192345395)
    ·
      refine ⟨117764915688835848288518093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78509943792557232192345395 117764915688835848288518093)
      ·
        refine ⟨44161843383313443108194285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117764915688835848288518093 44161843383313443108194285)
        ·
          refine ⟨16560691268742541165572857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44161843383313443108194285 16560691268742541165572857)
          ·
            refine ⟨12420518451556905874179643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16560691268742541165572857 12420518451556905874179643)
            ·
              refine ⟨18630777677335358811269465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12420518451556905874179643 18630777677335358811269465)
              ·
                refine ⟨13973083258001519108452099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18630777677335358811269465 13973083258001519108452099)
                ·
                  refine ⟨20959624887002278662678149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13973083258001519108452099 20959624887002278662678149)
                  ·
                    refine ⟨3929929666312927249252153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20959624887002278662678149 3929929666312927249252153)
                    ·
                      refine ⟨2947447249734695436939115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3929929666312927249252153 2947447249734695436939115)
                      ·
                        rfl

theorem cell23_5740133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_5740133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740133 prefixEnd_5740133 := by exact prefixLift 5740133
  have htrace : WordTrace (prefixWord ++ tailWord_5740133) baseStart_5740133 baseEnd_5740133 := by
    simpa [prefixWord, tailWord_5740133, baseEnd_5740133] using wordTrace_append hprefix tailTrace_5740133
  have hstable : (prefixWord ++ tailWord_5740133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740133).length < 2 ^ (prefixWord ++ tailWord_5740133).sum := by decide
  have hdescent : baseEnd_5740133 < baseStart_5740133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740136 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5740136 : Nat := 118140960795 + 5740136 * 2 ^ 59
def prefixEnd_5740136 : Nat := 4983230072969 + 3 ^ 40 * 5740136 * 2
def baseEnd_5740136 : Nat := 2947448790176658925201601

theorem tailTrace_5740136 : CollatzResearch.WordTrace tailWord_5740136 prefixEnd_5740136 2947448790176658925201601 := by
  unfold tailWord_5740136
  simp only [CollatzResearch.WordTrace]
  refine ⟨104679979766237542012640131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139573306354983389350186841 104679979766237542012640131)
  ·
    refine ⟨157019969649356313018960197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104679979766237542012640131 157019969649356313018960197)
    ·
      refine ⟨29441244309254308691055037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157019969649356313018960197 29441244309254308691055037)
      ·
        refine ⟨11040466615970365759145639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29441244309254308691055037 11040466615970365759145639)
        ·
          refine ⟨16560699923955548638718459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11040466615970365759145639 16560699923955548638718459)
          ·
            refine ⟨24841049885933322958077689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16560699923955548638718459 24841049885933322958077689)
            ·
              refine ⟨18630787414449992218558267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24841049885933322958077689 18630787414449992218558267)
              ·
                refine ⟨27946181121674988327837401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18630787414449992218558267 27946181121674988327837401)
                ·
                  refine ⟨20959635841256241245878051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27946181121674988327837401 20959635841256241245878051)
                  ·
                    refine ⟨31439453761884361868817077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20959635841256241245878051 31439453761884361868817077)
                    ·
                      refine ⟨2947448790176658925201601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31439453761884361868817077 2947448790176658925201601)
                      ·
                        rfl

theorem cell23_5740136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5740136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740136 prefixEnd_5740136 := by exact prefixLift 5740136
  have htrace : WordTrace (prefixWord ++ tailWord_5740136) baseStart_5740136 baseEnd_5740136 := by
    simpa [prefixWord, tailWord_5740136, baseEnd_5740136] using wordTrace_append hprefix tailTrace_5740136
  have hstable : (prefixWord ++ tailWord_5740136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740136).length < 2 ^ (prefixWord ++ tailWord_5740136).sum := by decide
  have hdescent : baseEnd_5740136 < baseStart_5740136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740169 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 4, 5]
def baseStart_5740169 : Nat := 118140960795 + 5740169 * 2 ^ 59
def prefixEnd_5740169 : Nat := 4983230072969 + 3 ^ 40 * 5740169 * 2
def baseEnd_5740169 : Nat := 982488578346085765362983

theorem tailTrace_5740169 : CollatzResearch.WordTrace tailWord_5740169 prefixEnd_5740169 982488578346085765362983 := by
  unfold tailWord_5740169
  simp only [CollatzResearch.WordTrace]
  refine ⟨209361163141355530661231561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139574108760903687107487707 209361163141355530661231561)
  ·
    refine ⟨157020872356016647995923671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209361163141355530661231561 157020872356016647995923671)
    ·
      refine ⟨235531308534024971993885507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157020872356016647995923671 235531308534024971993885507)
      ·
        refine ⟨353296962801037457990828261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235531308534024971993885507 353296962801037457990828261)
        ·
          refine ⟨66243180525194523373280299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 353296962801037457990828261 66243180525194523373280299)
          ·
            refine ⟨99364770787791785059920449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66243180525194523373280299 99364770787791785059920449)
            ·
              refine ⟨74523578090843838794940337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99364770787791785059920449 74523578090843838794940337)
              ·
                refine ⟨55892683568132879096205253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74523578090843838794940337 55892683568132879096205253)
                ·
                  refine ⟨10479878169024914830538485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55892683568132879096205253 10479878169024914830538485)
                  ·
                    refine ⟨982488578346085765362983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10479878169024914830538485 982488578346085765362983)
                    ·
                      rfl

theorem cell23_5740169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_5740169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740169 prefixEnd_5740169 := by exact prefixLift 5740169
  have htrace : WordTrace (prefixWord ++ tailWord_5740169) baseStart_5740169 baseEnd_5740169 := by
    simpa [prefixWord, tailWord_5740169, baseEnd_5740169] using wordTrace_append hprefix tailTrace_5740169
  have hstable : (prefixWord ++ tailWord_5740169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740169).length < 2 ^ (prefixWord ++ tailWord_5740169).sum := by decide
  have hdescent : baseEnd_5740169 < baseStart_5740169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740190 : List Nat := [4, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_5740190 : Nat := 118140960795 + 5740190 * 2 ^ 59
def prefixEnd_5740190 : Nat := 4983230072969 + 3 ^ 40 * 5740190 * 2
def baseEnd_5740190 : Nat := 327497390903555745991817

theorem tailTrace_5740190 : CollatzResearch.WordTrace tailWord_5740190 prefixEnd_5740190 327497390903555745991817 := by
  unfold tailWord_5740190
  simp only [CollatzResearch.WordTrace]
  refine ⟨26170241134284931405968253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139574619382852967498497349 26170241134284931405968253)
  ·
    refine ⟨9813840425356849277238095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26170241134284931405968253 9813840425356849277238095)
    ·
      refine ⟨14720760638035273915857143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9813840425356849277238095 14720760638035273915857143)
      ·
        refine ⟨22081140957052910873785715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14720760638035273915857143 22081140957052910873785715)
        ·
          refine ⟨33121711435579366310678573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22081140957052910873785715 33121711435579366310678573)
          ·
            refine ⟨12420641788342262366504465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33121711435579366310678573 12420641788342262366504465)
            ·
              refine ⟨9315481341256696774878349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12420641788342262366504465 9315481341256696774878349)
              ·
                refine ⟨3493305502971261290579381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9315481341256696774878349 3493305502971261290579381)
                ·
                  refine ⟨327497390903555745991817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3493305502971261290579381 327497390903555745991817)
                  ·
                    rfl

theorem cell23_5740190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_5740190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740190 prefixEnd_5740190 := by exact prefixLift 5740190
  have htrace : WordTrace (prefixWord ++ tailWord_5740190) baseStart_5740190 baseEnd_5740190 := by
    simpa [prefixWord, tailWord_5740190, baseEnd_5740190] using wordTrace_append hprefix tailTrace_5740190
  have hstable : (prefixWord ++ tailWord_5740190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740190).length < 2 ^ (prefixWord ++ tailWord_5740190).sum := by decide
  have hdescent : baseEnd_5740190 < baseStart_5740190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740250 : List Nat := [3, 1, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_5740250 : Nat := 118140960795 + 5740250 * 2 ^ 59
def prefixEnd_5740250 : Nat := 4983230072969 + 3 ^ 40 * 5740250 * 2
def baseEnd_5740250 : Nat := 982502442323757159725359

theorem tailTrace_5740250 : CollatzResearch.WordTrace tailWord_5740250 prefixEnd_5740250 982502442323757159725359 := by
  unfold tailWord_5740250
  simp only [CollatzResearch.WordTrace]
  refine ⟨52341029363515520373732551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139576078302708054329953469 52341029363515520373732551)
  ·
    refine ⟨78511544045273280560598827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52341029363515520373732551 78511544045273280560598827)
    ·
      refine ⟨117767316067909920840898241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78511544045273280560598827 117767316067909920840898241)
      ·
        refine ⟨88325487050932440630673681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117767316067909920840898241 88325487050932440630673681)
        ·
          refine ⟨66244115288199330473005261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88325487050932440630673681 66244115288199330473005261)
          ·
            refine ⟨24841543233074748927376973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66244115288199330473005261 24841543233074748927376973)
            ·
              refine ⟨9315578712403030847766365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24841543233074748927376973 9315578712403030847766365)
              ·
                refine ⟨3493342017151136567912387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9315578712403030847766365 3493342017151136567912387)
                ·
                  refine ⟨5240013025726704851868581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493342017151136567912387 5240013025726704851868581)
                  ·
                    refine ⟨982502442323757159725359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5240013025726704851868581 982502442323757159725359)
                    ·
                      rfl

theorem cell23_5740250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_5740250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740250 prefixEnd_5740250 := by exact prefixLift 5740250
  have htrace : WordTrace (prefixWord ++ tailWord_5740250) baseStart_5740250 baseEnd_5740250 := by
    simpa [prefixWord, tailWord_5740250, baseEnd_5740250] using wordTrace_append hprefix tailTrace_5740250
  have hstable : (prefixWord ++ tailWord_5740250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740250).length < 2 ^ (prefixWord ++ tailWord_5740250).sum := by decide
  have hdescent : baseEnd_5740250 < baseStart_5740250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740290 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_5740290 : Nat := 118140960795 + 5740290 * 2 ^ 59
def prefixEnd_5740290 : Nat := 4983230072969 + 3 ^ 40 * 5740290 * 2
def baseEnd_5740290 : Nat := 2947527866197451322675893

theorem tailTrace_5740290 : CollatzResearch.WordTrace tailWord_5740290 prefixEnd_5740290 2947527866197451322675893 := by
  unfold tailWord_5740290
  simp only [CollatzResearch.WordTrace]
  refine ⟨52341394093479292081596581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139577050915944778884257549 52341394093479292081596581)
  ·
    refine ⟨9814011392527367265299359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52341394093479292081596581 9814011392527367265299359)
    ·
      refine ⟨14721017088791050897949039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9814011392527367265299359 14721017088791050897949039)
      ·
        refine ⟨22081525633186576346923559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14721017088791050897949039 22081525633186576346923559)
        ·
          refine ⟨33122288449779864520385339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22081525633186576346923559 33122288449779864520385339)
          ·
            refine ⟨49683432674669796780578009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33122288449779864520385339 49683432674669796780578009)
            ·
              refine ⟨37262574506002347585433507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49683432674669796780578009 37262574506002347585433507)
              ·
                refine ⟨55893861759003521378150261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37262574506002347585433507 55893861759003521378150261)
                ·
                  refine ⟨5240049539906580129201587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55893861759003521378150261 5240049539906580129201587)
                  ·
                    refine ⟨7860074309859870193802381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5240049539906580129201587 7860074309859870193802381)
                    ·
                      refine ⟨2947527866197451322675893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7860074309859870193802381 2947527866197451322675893)
                      ·
                        rfl

theorem cell23_5740290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_5740290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740290 prefixEnd_5740290 := by exact prefixLift 5740290
  have htrace : WordTrace (prefixWord ++ tailWord_5740290) baseStart_5740290 baseEnd_5740290 := by
    simpa [prefixWord, tailWord_5740290, baseEnd_5740290] using wordTrace_append hprefix tailTrace_5740290
  have hstable : (prefixWord ++ tailWord_5740290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740290).length < 2 ^ (prefixWord ++ tailWord_5740290).sum := by decide
  have hdescent : baseEnd_5740290 < baseStart_5740290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740318 : List Nat := [4, 3, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5740318 : Nat := 118140960795 + 5740318 * 2 ^ 59
def prefixEnd_5740318 : Nat := 4983230072969 + 3 ^ 40 * 5740318 * 2
def baseEnd_5740318 : Nat := 982514081218592404375255

theorem tailTrace_5740318 : CollatzResearch.WordTrace tailWord_5740318 prefixEnd_5740318 982514081218592404375255 := by
  unfold tailWord_5740318
  simp only [CollatzResearch.WordTrace]
  refine ⟨26170824702226966138550701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139577731745210486072270405 26170824702226966138550701)
  ·
    refine ⟨9814059263335112301956513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26170824702226966138550701 9814059263335112301956513)
    ·
      refine ⟨7360544447501334226467385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9814059263335112301956513 7360544447501334226467385)
      ·
        refine ⟨5520408335626000669850539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7360544447501334226467385 5520408335626000669850539)
        ·
          refine ⟨8280612503439001004775809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5520408335626000669850539 8280612503439001004775809)
          ·
            refine ⟨6210459377579250753581857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8280612503439001004775809 6210459377579250753581857)
            ·
              refine ⟨4657844533184438065186393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6210459377579250753581857 4657844533184438065186393)
              ·
                refine ⟨3493383399888328548889795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657844533184438065186393 3493383399888328548889795)
                ·
                  refine ⟨5240075099832492823334693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493383399888328548889795 5240075099832492823334693)
                  ·
                    refine ⟨982514081218592404375255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5240075099832492823334693 982514081218592404375255)
                    ·
                      rfl

theorem cell23_5740318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5740318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740318 prefixEnd_5740318 := by exact prefixLift 5740318
  have htrace : WordTrace (prefixWord ++ tailWord_5740318) baseStart_5740318 baseEnd_5740318 := by
    simpa [prefixWord, tailWord_5740318, baseEnd_5740318] using wordTrace_append hprefix tailTrace_5740318
  have hstable : (prefixWord ++ tailWord_5740318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740318).length < 2 ^ (prefixWord ++ tailWord_5740318).sum := by decide
  have hdescent : baseEnd_5740318 < baseStart_5740318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740323 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 2, 4]
def baseStart_5740323 : Nat := 118140960795 + 5740323 * 2 ^ 59
def prefixEnd_5740323 : Nat := 4983230072969 + 3 ^ 40 * 5740323 * 2
def baseEnd_5740323 : Nat := 982514937019683231187747

theorem tailTrace_5740323 : CollatzResearch.WordTrace tailWord_5740323 prefixEnd_5740323 982514937019683231187747 := by
  unfold tailWord_5740323
  simp only [CollatzResearch.WordTrace]
  refine ⟨209366779982797614962337623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139577853321865076641558415 209366779982797614962337623)
  ·
    refine ⟨314050169974196422443506435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209366779982797614962337623 314050169974196422443506435)
    ·
      refine ⟨471075254961294633665259653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314050169974196422443506435 471075254961294633665259653)
      ·
        refine ⟨88326610305242743812236185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 471075254961294633665259653 88326610305242743812236185)
        ·
          refine ⟨66244957728932057859177139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88326610305242743812236185 66244957728932057859177139)
          ·
            refine ⟨99367436593398086788765709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66244957728932057859177139 99367436593398086788765709)
            ·
              refine ⟨37262788722524282545787141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99367436593398086788765709 37262788722524282545787141)
              ·
                refine ⟨6986772885473302977335089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37262788722524282545787141 6986772885473302977335089)
                ·
                  refine ⟨5240079664104977233001317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6986772885473302977335089 5240079664104977233001317)
                  ·
                    refine ⟨982514937019683231187747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5240079664104977233001317 982514937019683231187747)
                    ·
                      rfl

theorem cell23_5740323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2, 4].length) (baseStart_5740323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740323 prefixEnd_5740323 := by exact prefixLift 5740323
  have htrace : WordTrace (prefixWord ++ tailWord_5740323) baseStart_5740323 baseEnd_5740323 := by
    simpa [prefixWord, tailWord_5740323, baseEnd_5740323] using wordTrace_append hprefix tailTrace_5740323
  have hstable : (prefixWord ++ tailWord_5740323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740323).length < 2 ^ (prefixWord ++ tailWord_5740323).sum := by decide
  have hdescent : baseEnd_5740323 < baseStart_5740323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740324 : List Nat := [2, 3, 1, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_5740324 : Nat := 118140960795 + 5740324 * 2 ^ 59
def prefixEnd_5740324 : Nat := 4983230072969 + 3 ^ 40 * 5740324 * 2
def baseEnd_5740324 : Nat := 2947545324539704189650737

theorem tailTrace_5740324 : CollatzResearch.WordTrace tailWord_5740324 prefixEnd_5740324 2947545324539704189650737 := by
  unfold tailWord_5740324
  simp only [CollatzResearch.WordTrace]
  refine ⟨104683408227896996066562013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139577877637195994755416017 104683408227896996066562013)
  ·
    refine ⟨39256278085461373524960755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104683408227896996066562013 39256278085461373524960755)
    ·
      refine ⟨58884417128192060287441133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39256278085461373524960755 58884417128192060287441133)
      ·
        refine ⟨22081656423072022607790425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58884417128192060287441133 22081656423072022607790425)
        ·
          refine ⟨16561242317304016955842819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22081656423072022607790425 16561242317304016955842819)
          ·
            refine ⟨24841863475956025433764229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16561242317304016955842819 24841863475956025433764229)
            ·
              refine ⟨4657849401741754768830793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24841863475956025433764229 4657849401741754768830793)
              ·
                refine ⟨3493387051306316076623095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4657849401741754768830793 3493387051306316076623095)
                ·
                  refine ⟨5240080576959474114934643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493387051306316076623095 5240080576959474114934643)
                  ·
                    refine ⟨7860120865439211172401965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5240080576959474114934643 7860120865439211172401965)
                    ·
                      refine ⟨2947545324539704189650737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7860120865439211172401965 2947545324539704189650737)
                      ·
                        rfl

theorem cell23_5740324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_5740324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740324 prefixEnd_5740324 := by exact prefixLift 5740324
  have htrace : WordTrace (prefixWord ++ tailWord_5740324) baseStart_5740324 baseEnd_5740324 := by
    simpa [prefixWord, tailWord_5740324, baseEnd_5740324] using wordTrace_append hprefix tailTrace_5740324
  have hstable : (prefixWord ++ tailWord_5740324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740324).length < 2 ^ (prefixWord ++ tailWord_5740324).sum := by decide
  have hdescent : baseEnd_5740324 < baseStart_5740324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740340 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_5740340 : Nat := 118140960795 + 5740340 * 2 ^ 59
def prefixEnd_5740340 : Nat := 4983230072969 + 3 ^ 40 * 5740340 * 2
def baseEnd_5740340 : Nat := 982517846743392042350221

theorem tailTrace_5740340 : CollatzResearch.WordTrace tailWord_5740340 prefixEnd_5740340 982517846743392042350221 := by
  unfold tailWord_5740340
  simp only [CollatzResearch.WordTrace]
  refine ⟨104683700011868013432853237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139578266682490684577137649 104683700011868013432853237)
  ·
    refine ⟨9814096876112626259329991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104683700011868013432853237 9814096876112626259329991)
    ·
      refine ⟨14721145314168939388994987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9814096876112626259329991 14721145314168939388994987)
      ·
        refine ⟨22081717971253409083492481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14721145314168939388994987 22081717971253409083492481)
        ·
          refine ⟨16561288478440056812619361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22081717971253409083492481 16561288478440056812619361)
          ·
            refine ⟨12420966358830042609464521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16561288478440056812619361 12420966358830042609464521)
            ·
              refine ⟨9315724769122531957098391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12420966358830042609464521 9315724769122531957098391)
              ·
                refine ⟨13973587153683797935647587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9315724769122531957098391 13973587153683797935647587)
                ·
                  refine ⟨20960380730525696903471381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13973587153683797935647587 20960380730525696903471381)
                  ·
                    refine ⟨982517846743392042350221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20960380730525696903471381 982517846743392042350221)
                    ·
                      rfl

theorem cell23_5740340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_5740340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740340 prefixEnd_5740340 := by exact prefixLift 5740340
  have htrace : WordTrace (prefixWord ++ tailWord_5740340) baseStart_5740340 baseEnd_5740340 := by
    simpa [prefixWord, tailWord_5740340, baseEnd_5740340] using wordTrace_append hprefix tailTrace_5740340
  have hstable : (prefixWord ++ tailWord_5740340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740340).length < 2 ^ (prefixWord ++ tailWord_5740340).sum := by decide
  have hdescent : baseEnd_5740340 < baseStart_5740340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740350 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_5740350 : Nat := 118140960795 + 5740350 * 2 ^ 59
def prefixEnd_5740350 : Nat := 4983230072969 + 3 ^ 40 * 5740350 * 2
def baseEnd_5740350 : Nat := 2947558675036721087925617

theorem tailTrace_5740350 : CollatzResearch.WordTrace tailWord_5740350 prefixEnd_5740350 2947558675036721087925617 := by
  unfold tailWord_5740350
  simp only [CollatzResearch.WordTrace]
  refine ⟨26170970594212474821696313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139578509835799865715713669 26170970594212474821696313)
  ·
    refine ⟨19628227945659356116272235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26170970594212474821696313 19628227945659356116272235)
    ·
      refine ⟨29442341918489034174408353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19628227945659356116272235 29442341918489034174408353)
      ·
        refine ⟨22081756438866775630806265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29442341918489034174408353 22081756438866775630806265)
        ·
          refine ⟨16561317329150081723104699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22081756438866775630806265 16561317329150081723104699)
          ·
            refine ⟨24841975993725122584657049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16561317329150081723104699 24841975993725122584657049)
            ·
              refine ⟨18631481995293841938492787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24841975993725122584657049 18631481995293841938492787)
              ·
                refine ⟨27947222992940762907739181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18631481995293841938492787 27947222992940762907739181)
                ·
                  refine ⟨10480208622352786090402193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27947222992940762907739181 10480208622352786090402193)
                  ·
                    refine ⟨7860156466764589567801645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10480208622352786090402193 7860156466764589567801645)
                    ·
                      refine ⟨2947558675036721087925617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7860156466764589567801645 2947558675036721087925617)
                      ·
                        rfl

theorem cell23_5740350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_5740350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740350 prefixEnd_5740350 := by exact prefixLift 5740350
  have htrace : WordTrace (prefixWord ++ tailWord_5740350) baseStart_5740350 baseEnd_5740350 := by
    simpa [prefixWord, tailWord_5740350, baseEnd_5740350] using wordTrace_append hprefix tailTrace_5740350
  have hstable : (prefixWord ++ tailWord_5740350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740350).length < 2 ^ (prefixWord ++ tailWord_5740350).sum := by decide
  have hdescent : baseEnd_5740350 < baseStart_5740350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740364 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 1, 1, 4]
def baseStart_5740364 : Nat := 118140960795 + 5740364 * 2 ^ 59
def prefixEnd_5740364 : Nat := 4983230072969 + 3 ^ 40 * 5740364 * 2
def baseEnd_5740364 : Nat := 2947565863765884033150553

theorem tailTrace_5740364 : CollatzResearch.WordTrace tailWord_5740364 prefixEnd_5740364 2947565863765884033150553 := by
  unfold tailWord_5740364
  simp only [CollatzResearch.WordTrace]
  refine ⟨104684137687824539482290073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139578850250432719309720097 104684137687824539482290073)
  ·
    refine ⟨78513103265868404611717555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104684137687824539482290073 78513103265868404611717555)
    ·
      refine ⟨117769654898802606917576333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78513103265868404611717555 117769654898802606917576333)
      ·
        refine ⟨44163620587050977594091125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117769654898802606917576333 44163620587050977594091125)
        ·
          refine ⟨4140339430036029149446043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44163620587050977594091125 4140339430036029149446043)
          ·
            refine ⟨6210509145054043724169065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140339430036029149446043 6210509145054043724169065)
            ·
              refine ⟨4657881858790532793126799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6210509145054043724169065 4657881858790532793126799)
              ·
                refine ⟨6986822788185799189690199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4657881858790532793126799 6986822788185799189690199)
                ·
                  refine ⟨10480234182278698784535299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6986822788185799189690199 10480234182278698784535299)
                  ·
                    refine ⟨15720351273418048176802949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10480234182278698784535299 15720351273418048176802949)
                    ·
                      refine ⟨2947565863765884033150553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15720351273418048176802949 2947565863765884033150553)
                      ·
                        rfl

theorem cell23_5740364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_5740364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740364 prefixEnd_5740364 := by exact prefixLift 5740364
  have htrace : WordTrace (prefixWord ++ tailWord_5740364) baseStart_5740364 baseEnd_5740364 := by
    simpa [prefixWord, tailWord_5740364, baseEnd_5740364] using wordTrace_append hprefix tailTrace_5740364
  have hstable : (prefixWord ++ tailWord_5740364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740364).length < 2 ^ (prefixWord ++ tailWord_5740364).sum := by decide
  have hdescent : baseEnd_5740364 < baseStart_5740364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740394 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5740394 : Nat := 118140960795 + 5740394 * 2 ^ 59
def prefixEnd_5740394 : Nat := 4983230072969 + 3 ^ 40 * 5740394 * 2
def baseEnd_5740394 : Nat := 2947581268185518915775415

theorem tailTrace_5740394 : CollatzResearch.WordTrace tailWord_5740394 prefixEnd_5740394 2947581268185518915775415 := by
  unfold tailWord_5740394
  simp only [CollatzResearch.WordTrace]
  refine ⟨52342342391385098522043059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139579579710360262725448157 52342342391385098522043059)
  ·
    refine ⟨78513513587077647783064589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52342342391385098522043059 78513513587077647783064589)
    ·
      refine ⟨29442567595154117918649221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78513513587077647783064589 29442567595154117918649221)
      ·
        refine ⟨5520481424091397109746729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29442567595154117918649221 5520481424091397109746729)
        ·
          refine ⟨4140361068068547832310047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5520481424091397109746729 4140361068068547832310047)
          ·
            refine ⟨6210541602102821748465071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140361068068547832310047 6210541602102821748465071)
            ·
              refine ⟨9315812403154232622697607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6210541602102821748465071 9315812403154232622697607)
              ·
                refine ⟨13973718604731348934046411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9315812403154232622697607 13973718604731348934046411)
                ·
                  refine ⟨20960577907097023401069617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13973718604731348934046411 20960577907097023401069617)
                  ·
                    refine ⟨15720433430322767550802213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20960577907097023401069617 15720433430322767550802213)
                    ·
                      refine ⟨2947581268185518915775415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15720433430322767550802213 2947581268185518915775415)
                      ·
                        rfl

theorem cell23_5740394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5740394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740394 prefixEnd_5740394 := by exact prefixLift 5740394
  have htrace : WordTrace (prefixWord ++ tailWord_5740394) baseStart_5740394 baseEnd_5740394 := by
    simpa [prefixWord, tailWord_5740394, baseEnd_5740394] using wordTrace_append hprefix tailTrace_5740394
  have hstable : (prefixWord ++ tailWord_5740394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740394).length < 2 ^ (prefixWord ++ tailWord_5740394).sum := by decide
  have hdescent : baseEnd_5740394 < baseStart_5740394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740420 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_5740420 : Nat := 118140960795 + 5740420 * 2 ^ 59
def prefixEnd_5740420 : Nat := 4983230072969 + 3 ^ 40 * 5740420 * 2
def baseEnd_5740420 : Nat := 2947594618682535814050295

theorem tailTrace_5740420 : CollatzResearch.WordTrace tailWord_5740420 prefixEnd_5740420 2947594618682535814050295 := by
  unfold tailWord_5740420
  simp only [CollatzResearch.WordTrace]
  refine ⟨104685158931723100264309357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139580211908964133685745809 104685158931723100264309357)
  ·
    refine ⟨39256934599396162599116009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104685158931723100264309357 39256934599396162599116009)
    ·
      refine ⟨29442700949547121949337007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39256934599396162599116009 29442700949547121949337007)
      ·
        refine ⟨44164051424320682924005511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29442700949547121949337007 44164051424320682924005511)
        ·
          refine ⟨66246077136481024386008267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44164051424320682924005511 66246077136481024386008267)
          ·
            refine ⟨99369115704721536579012401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66246077136481024386008267 99369115704721536579012401)
            ·
              refine ⟨74526836778541152434259301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99369115704721536579012401 74526836778541152434259301)
              ·
                refine ⟨13973781895976466081423619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74526836778541152434259301 13973781895976466081423619)
                ·
                  refine ⟨20960672843964699122135429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13973781895976466081423619 20960672843964699122135429)
                  ·
                    refine ⟨3930126158243381085400393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20960672843964699122135429 3930126158243381085400393)
                    ·
                      refine ⟨2947594618682535814050295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930126158243381085400393 2947594618682535814050295)
                      ·
                        rfl

theorem cell23_5740420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_5740420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740420 prefixEnd_5740420 := by exact prefixLift 5740420
  have htrace : WordTrace (prefixWord ++ tailWord_5740420) baseStart_5740420 baseEnd_5740420 := by
    simpa [prefixWord, tailWord_5740420, baseEnd_5740420] using wordTrace_append hprefix tailTrace_5740420
  have hstable : (prefixWord ++ tailWord_5740420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740420).length < 2 ^ (prefixWord ++ tailWord_5740420).sum := by decide
  have hdescent : baseEnd_5740420 < baseStart_5740420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740437 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_5740437 : Nat := 118140960795 + 5740437 * 2 ^ 59
def prefixEnd_5740437 : Nat := 4983230072969 + 3 ^ 40 * 5740437 * 2
def baseEnd_5740437 : Nat := 2947603347853662247537717

theorem tailTrace_5740437 : CollatzResearch.WordTrace tailWord_5740437 prefixEnd_5740437 2947603347853662247537717 := by
  unfold tailWord_5740437
  simp only [CollatzResearch.WordTrace]
  refine ⟨209370937904384612431987565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139580625269589741621325043 209370937904384612431987565)
  ·
    refine ⟨78514101714144229661995337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209370937904384612431987565 78514101714144229661995337)
    ·
      refine ⟨58885576285608172246496503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78514101714144229661995337 58885576285608172246496503)
      ·
        refine ⟨88328364428412258369744755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58885576285608172246496503 88328364428412258369744755)
        ·
          refine ⟨132492546642618387554617133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88328364428412258369744755 132492546642618387554617133)
          ·
            refine ⟨49684704990981895332981425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132492546642618387554617133 49684704990981895332981425)
            ·
              refine ⟨37263528743236421499736069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49684704990981895332981425 37263528743236421499736069)
              ·
                refine ⟨6986911639356829031200513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37263528743236421499736069 6986911639356829031200513)
                ·
                  refine ⟨5240183729517621773400385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6986911639356829031200513 5240183729517621773400385)
                  ·
                    refine ⟨3930137797138216330050289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240183729517621773400385 3930137797138216330050289)
                    ·
                      refine ⟨2947603347853662247537717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930137797138216330050289 2947603347853662247537717)
                      ·
                        rfl

theorem cell23_5740437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_5740437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740437 prefixEnd_5740437 := by exact prefixLift 5740437
  have htrace : WordTrace (prefixWord ++ tailWord_5740437) baseStart_5740437 baseEnd_5740437 := by
    simpa [prefixWord, tailWord_5740437, baseEnd_5740437] using wordTrace_append hprefix tailTrace_5740437
  have hstable : (prefixWord ++ tailWord_5740437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740437).length < 2 ^ (prefixWord ++ tailWord_5740437).sum := by decide
  have hdescent : baseEnd_5740437 < baseStart_5740437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740453 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_5740453 : Nat := 118140960795 + 5740453 * 2 ^ 59
def prefixEnd_5740453 : Nat := 4983230072969 + 3 ^ 40 * 5740453 * 2
def baseEnd_5740453 : Nat := 2947611563544134184937643

theorem tailTrace_5740453 : CollatzResearch.WordTrace tailWord_5740453 prefixEnd_5740453 2947611563544134184937643 := by
  unfold tailWord_5740453
  simp only [CollatzResearch.WordTrace]
  refine ⟨209371521472326647164570013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139581014314884431443046675 209371521472326647164570013)
  ·
    refine ⟨78514320552122492686713755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209371521472326647164570013 78514320552122492686713755)
    ·
      refine ⟨117771480828183739030070633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78514320552122492686713755 117771480828183739030070633)
      ·
        refine ⟨88328610621137804272552975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117771480828183739030070633 88328610621137804272552975)
        ·
          refine ⟨132492915931706706408829463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88328610621137804272552975 132492915931706706408829463)
          ·
            refine ⟨198739373897560059613244195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132492915931706706408829463 198739373897560059613244195)
            ·
              refine ⟨298109060846340089419866293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198739373897560059613244195 298109060846340089419866293)
              ·
                refine ⟨27947724454344383383112465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 298109060846340089419866293 27947724454344383383112465)
                ·
                  refine ⟨20960793340758287537334349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27947724454344383383112465 20960793340758287537334349)
                  ·
                    refine ⟨7860297502784357826500381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20960793340758287537334349 7860297502784357826500381)
                    ·
                      refine ⟨2947611563544134184937643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7860297502784357826500381 2947611563544134184937643)
                      ·
                        rfl

theorem cell23_5740453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_5740453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740453 prefixEnd_5740453 := by exact prefixLift 5740453
  have htrace : WordTrace (prefixWord ++ tailWord_5740453) baseStart_5740453 baseEnd_5740453 := by
    simpa [prefixWord, tailWord_5740453, baseEnd_5740453] using wordTrace_append hprefix tailTrace_5740453
  have hstable : (prefixWord ++ tailWord_5740453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740453).length < 2 ^ (prefixWord ++ tailWord_5740453).sum := by decide
  have hdescent : baseEnd_5740453 < baseStart_5740453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740537 : List Nat := [1, 2, 1, 3, 1, 4, 1, 5, 1, 4]
def baseStart_5740537 : Nat := 118140960795 + 5740537 * 2 ^ 59
def prefixEnd_5740537 : Nat := 4983230072969 + 3 ^ 40 * 5740537 * 2
def baseEnd_5740537 : Nat := 982551565306370618762419

theorem tailTrace_5740537 : CollatzResearch.WordTrace tailWord_5740537 prefixEnd_5740537 982551565306370618762419 := by
  unfold tailWord_5740537
  simp only [CollatzResearch.WordTrace]
  refine ⟨209374585204022329510627865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139583056802681553007085243 209374585204022329510627865)
  ·
    refine ⟨157030938903016747132970899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209374585204022329510627865 157030938903016747132970899)
    ·
      refine ⟨235546408354525120699456349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157030938903016747132970899 235546408354525120699456349)
      ·
        refine ⟨88329903132946920262296131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235546408354525120699456349 88329903132946920262296131)
        ·
          refine ⟨132494854699420380393444197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88329903132946920262296131 132494854699420380393444197)
          ·
            refine ⟨24842785256141321323770787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132494854699420380393444197 24842785256141321323770787)
            ·
              refine ⟨37264177884211981985656181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24842785256141321323770787 37264177884211981985656181)
              ·
                refine ⟨3493516676644873311155267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37264177884211981985656181 3493516676644873311155267)
                ·
                  refine ⟨5240275014967309966732901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493516676644873311155267 5240275014967309966732901)
                  ·
                    refine ⟨982551565306370618762419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5240275014967309966732901 982551565306370618762419)
                    ·
                      rfl

theorem cell23_5740537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 1, 4].length) (baseStart_5740537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740537 prefixEnd_5740537 := by exact prefixLift 5740537
  have htrace : WordTrace (prefixWord ++ tailWord_5740537) baseStart_5740537 baseEnd_5740537 := by
    simpa [prefixWord, tailWord_5740537, baseEnd_5740537] using wordTrace_append hprefix tailTrace_5740537
  have hstable : (prefixWord ++ tailWord_5740537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740537).length < 2 ^ (prefixWord ++ tailWord_5740537).sum := by decide
  have hdescent : baseEnd_5740537 < baseStart_5740537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740543 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 3]
def baseStart_5740543 : Nat := 118140960795 + 5740543 * 2 ^ 59
def prefixEnd_5740543 : Nat := 4983230072969 + 3 ^ 40 * 5740543 * 2
def baseEnd_5740543 : Nat := 2947657776803038832812229

theorem tailTrace_5740543 : CollatzResearch.WordTrace tailWord_5740543 prefixEnd_5740543 2947657776803038832812229 := by
  unfold tailWord_5740543
  simp only [CollatzResearch.WordTrace]
  refine ⟨209374804042000592535346283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139583202694667061690230855 209374804042000592535346283)
  ·
    refine ⟨314062206063000888803019425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209374804042000592535346283 314062206063000888803019425)
    ·
      refine ⟨235546654547250666602264569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314062206063000888803019425 235546654547250666602264569)
      ·
        refine ⟨176659990910437999951698427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235546654547250666602264569 176659990910437999951698427)
        ·
          refine ⟨264989986365656999927547641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176659990910437999951698427 264989986365656999927547641)
          ·
            refine ⟨198742489774242749945660731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264989986365656999927547641 198742489774242749945660731)
            ·
              refine ⟨298113734661364124918491097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198742489774242749945660731 298113734661364124918491097)
              ·
                refine ⟨223585300996023093688868323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298113734661364124918491097 223585300996023093688868323)
                ·
                  refine ⟨335377951494034640533302485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223585300996023093688868323 335377951494034640533302485)
                  ·
                    refine ⟨7860420738141436887499277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 335377951494034640533302485 7860420738141436887499277)
                    ·
                      refine ⟨2947657776803038832812229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7860420738141436887499277 2947657776803038832812229)
                      ·
                        rfl

theorem cell23_5740543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_5740543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740543 prefixEnd_5740543 := by exact prefixLift 5740543
  have htrace : WordTrace (prefixWord ++ tailWord_5740543) baseStart_5740543 baseEnd_5740543 := by
    simpa [prefixWord, tailWord_5740543, baseEnd_5740543] using wordTrace_append hprefix tailTrace_5740543
  have hstable : (prefixWord ++ tailWord_5740543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740543).length < 2 ^ (prefixWord ++ tailWord_5740543).sum := by decide
  have hdescent : baseEnd_5740543 < baseStart_5740543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740560 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 7, 1, 3]
def baseStart_5740560 : Nat := 118140960795 + 5740560 * 2 ^ 59
def prefixEnd_5740560 : Nat := 4983230072969 + 3 ^ 40 * 5740560 * 2
def baseEnd_5740560 : Nat := 2947666505974165266299651

theorem tailTrace_5740560 : CollatzResearch.WordTrace tailWord_5740560 prefixEnd_5740560 2947666505974165266299651 := by
  unfold tailWord_5740560
  simp only [CollatzResearch.WordTrace]
  refine ⟨104687712041469502219357567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139583616055292669625810089 104687712041469502219357567)
  ·
    refine ⟨157031568062204253329036351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104687712041469502219357567 157031568062204253329036351)
    ·
      refine ⟨235547352093306379993554527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157031568062204253329036351 235547352093306379993554527)
      ·
        refine ⟨353321028139959569990331791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235547352093306379993554527 353321028139959569990331791)
        ·
          refine ⟨529981542209939354985497687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353321028139959569990331791 529981542209939354985497687)
          ·
            refine ⟨794972313314909032478246531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529981542209939354985497687 794972313314909032478246531)
            ·
              refine ⟨1192458469972363548717369797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794972313314909032478246531 1192458469972363548717369797)
              ·
                refine ⟨223585963119818165384506837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1192458469972363548717369797 223585963119818165384506837)
                ·
                  refine ⟨5240296010620738251199379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 223585963119818165384506837 5240296010620738251199379)
                  ·
                    refine ⟨7860444015931107376799069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5240296010620738251199379 7860444015931107376799069)
                    ·
                      refine ⟨2947666505974165266299651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7860444015931107376799069 2947666505974165266299651)
                      ·
                        rfl

theorem cell23_5740560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 1, 3].length) (baseStart_5740560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740560 prefixEnd_5740560 := by exact prefixLift 5740560
  have htrace : WordTrace (prefixWord ++ tailWord_5740560) baseStart_5740560 baseEnd_5740560 := by
    simpa [prefixWord, tailWord_5740560, baseEnd_5740560] using wordTrace_append hprefix tailTrace_5740560
  have hstable : (prefixWord ++ tailWord_5740560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740560).length < 2 ^ (prefixWord ++ tailWord_5740560).sum := by decide
  have hdescent : baseEnd_5740560 < baseStart_5740560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740563 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 5, 5]
def baseStart_5740563 : Nat := 118140960795 + 5740563 * 2 ^ 59
def prefixEnd_5740563 : Nat := 4983230072969 + 3 ^ 40 * 5740563 * 2
def baseEnd_5740563 : Nat := 982556015472042918187379

theorem tailTrace_5740563 : CollatzResearch.WordTrace tailWord_5740563 prefixEnd_5740563 982556015472042918187379 := by
  unfold tailWord_5740563
  simp only [CollatzResearch.WordTrace]
  refine ⟨209375533501928135951074343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139583689001285423967382895 209375533501928135951074343)
  ·
    refine ⟨314063300252892203926611515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209375533501928135951074343 314063300252892203926611515)
    ·
      refine ⟨471094950379338305889917273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314063300252892203926611515 471094950379338305889917273)
      ·
        refine ⟨353321212784503729417437955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471094950379338305889917273 353321212784503729417437955)
        ·
          refine ⟨529981819176755594126156933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353321212784503729417437955 529981819176755594126156933)
          ·
            refine ⟨99371591095641673898654425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 529981819176755594126156933 99371591095641673898654425)
            ·
              refine ⟨74528693321731255423990819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99371591095641673898654425 74528693321731255423990819)
              ·
                refine ⟨111793039982596883135986229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74528693321731255423990819 111793039982596883135986229)
                ·
                  refine ⟨10480597498368457793998709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111793039982596883135986229 10480597498368457793998709)
                  ·
                    refine ⟨982556015472042918187379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10480597498368457793998709 982556015472042918187379)
                    ·
                      rfl

theorem cell23_5740563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 5].length) (baseStart_5740563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740563 prefixEnd_5740563 := by exact prefixLift 5740563
  have htrace : WordTrace (prefixWord ++ tailWord_5740563) baseStart_5740563 baseEnd_5740563 := by
    simpa [prefixWord, tailWord_5740563, baseEnd_5740563] using wordTrace_append hprefix tailTrace_5740563
  have hstable : (prefixWord ++ tailWord_5740563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740563).length < 2 ^ (prefixWord ++ tailWord_5740563).sum := by decide
  have hdescent : baseEnd_5740563 < baseStart_5740563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740603 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5]
def baseStart_5740603 : Nat := 118140960795 + 5740603 * 2 ^ 59
def prefixEnd_5740603 : Nat := 4983230072969 + 3 ^ 40 * 5740603 * 2
def baseEnd_5740603 : Nat := 2947688585642308598061953

theorem tailTrace_5740603 : CollatzResearch.WordTrace tailWord_5740603 prefixEnd_5740603 2947688585642308598061953 := by
  unfold tailWord_5740603
  simp only [CollatzResearch.WordTrace]
  refine ⟨209376992421783222782530463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139584661614522148521686975 209376992421783222782530463)
  ·
    refine ⟨314065488632674834173795695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209376992421783222782530463 314065488632674834173795695)
    ·
      refine ⟨471098232949012251260693543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314065488632674834173795695 471098232949012251260693543)
      ·
        refine ⟨706647349423518376891040315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471098232949012251260693543 706647349423518376891040315)
        ·
          refine ⟨1059971024135277565336560473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706647349423518376891040315 1059971024135277565336560473)
          ·
            refine ⟨794978268101458174002420355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1059971024135277565336560473 794978268101458174002420355)
            ·
              refine ⟨1192467402152187261003630533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794978268101458174002420355 1192467402152187261003630533)
              ·
                refine ⟨223587637903535111438180725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1192467402152187261003630533 223587637903535111438180725)
                ·
                  refine ⟨20961341053456416697329443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223587637903535111438180725 20961341053456416697329443)
                  ·
                    refine ⟨31442011580184625045994165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20961341053456416697329443 31442011580184625045994165)
                    ·
                      refine ⟨2947688585642308598061953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31442011580184625045994165 2947688585642308598061953)
                      ·
                        rfl

theorem cell23_5740603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_5740603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740603 prefixEnd_5740603 := by exact prefixLift 5740603
  have htrace : WordTrace (prefixWord ++ tailWord_5740603) baseStart_5740603 baseEnd_5740603 := by
    simpa [prefixWord, tailWord_5740603, baseEnd_5740603] using wordTrace_append hprefix tailTrace_5740603
  have hstable : (prefixWord ++ tailWord_5740603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740603).length < 2 ^ (prefixWord ++ tailWord_5740603).sum := by decide
  have hdescent : baseEnd_5740603 < baseStart_5740603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740620 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5740620 : Nat := 118140960795 + 5740620 * 2 ^ 59
def prefixEnd_5740620 : Nat := 4983230072969 + 3 ^ 40 * 5740620 * 2
def baseEnd_5740620 : Nat := 2947697314813435031549375

theorem tailTrace_5740620 : CollatzResearch.WordTrace tailWord_5740620 prefixEnd_5740620 2947697314813435031549375 := by
  unfold tailWord_5740620
  simp only [CollatzResearch.WordTrace]
  refine ⟨104688806231360817342949657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139585074975147756457266209 104688806231360817342949657)
  ·
    refine ⟨78516604673520613007212243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104688806231360817342949657 78516604673520613007212243)
    ·
      refine ⟨117774907010280919510818365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78516604673520613007212243 117774907010280919510818365)
      ·
        refine ⟨44165590128855344816556887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117774907010280919510818365 44165590128855344816556887)
        ·
          refine ⟨66248385193283017224835331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44165590128855344816556887 66248385193283017224835331)
          ·
            refine ⟨99372577789924525837252997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66248385193283017224835331 99372577789924525837252997)
            ·
              refine ⟨18632358335610848594484937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99372577789924525837252997 18632358335610848594484937)
              ·
                refine ⟨13974268751708136445863703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18632358335610848594484937 13974268751708136445863703)
                ·
                  refine ⟨20961403127562204668795555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13974268751708136445863703 20961403127562204668795555)
                  ·
                    refine ⟨31442104691343307003193333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20961403127562204668795555 31442104691343307003193333)
                    ·
                      refine ⟨2947697314813435031549375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31442104691343307003193333 2947697314813435031549375)
                      ·
                        rfl

theorem cell23_5740620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5740620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740620 prefixEnd_5740620 := by exact prefixLift 5740620
  have htrace : WordTrace (prefixWord ++ tailWord_5740620) baseStart_5740620 baseEnd_5740620 := by
    simpa [prefixWord, tailWord_5740620, baseEnd_5740620] using wordTrace_append hprefix tailTrace_5740620
  have hstable : (prefixWord ++ tailWord_5740620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740620).length < 2 ^ (prefixWord ++ tailWord_5740620).sum := by decide
  have hdescent : baseEnd_5740620 < baseStart_5740620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740668 : List Nat := [2, 2, 2, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_5740668 : Nat := 118140960795 + 5740668 * 2 ^ 59
def prefixEnd_5740668 : Nat := 4983230072969 + 3 ^ 40 * 5740668 * 2
def baseEnd_5740668 : Nat := 2947721961884850843749155

theorem tailTrace_5740668 : CollatzResearch.WordTrace tailWord_5740668 prefixEnd_5740668 2947721961884850843749155 := by
  unfold tailWord_5740668
  simp only [CollatzResearch.WordTrace]
  refine ⟨104689681583273869441823329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139586242111031825922431105 104689681583273869441823329)
  ·
    refine ⟨78517261187455402081367497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104689681583273869441823329 78517261187455402081367497)
    ·
      refine ⟨58887945890591551561025623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78517261187455402081367497 58887945890591551561025623)
      ·
        refine ⟨88331918835887327341538435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58887945890591551561025623 88331918835887327341538435)
        ·
          refine ⟨132497878253830991012307653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88331918835887327341538435 132497878253830991012307653)
          ·
            refine ⟨24843352172593310814807685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132497878253830991012307653 24843352172593310814807685)
            ·
              refine ⟨4658128532361245777776441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24843352172593310814807685 4658128532361245777776441)
              ·
                refine ⟨3493596399270934333332331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4658128532361245777776441 3493596399270934333332331)
                ·
                  refine ⟨5240394598906401499998497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493596399270934333332331 5240394598906401499998497)
                  ·
                    refine ⟨3930295949179801124998873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240394598906401499998497 3930295949179801124998873)
                    ·
                      refine ⟨2947721961884850843749155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930295949179801124998873 2947721961884850843749155)
                      ·
                        rfl

theorem cell23_5740668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_5740668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740668 prefixEnd_5740668 := by exact prefixLift 5740668
  have htrace : WordTrace (prefixWord ++ tailWord_5740668) baseStart_5740668 baseEnd_5740668 := by
    simpa [prefixWord, tailWord_5740668, baseEnd_5740668] using wordTrace_append hprefix tailTrace_5740668
  have hstable : (prefixWord ++ tailWord_5740668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740668).length < 2 ^ (prefixWord ++ tailWord_5740668).sum := by decide
  have hdescent : baseEnd_5740668 < baseStart_5740668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740700 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_5740700 : Nat := 118140960795 + 5740700 * 2 ^ 59
def prefixEnd_5740700 : Nat := 4983230072969 + 3 ^ 40 * 5740700 * 2
def baseEnd_5740700 : Nat := 982579464421931572849669

theorem tailTrace_5740700 : CollatzResearch.WordTrace tailWord_5740700 prefixEnd_5740700 982579464421931572849669 := by
  unfold tailWord_5740700
  simp only [CollatzResearch.WordTrace]
  refine ⟨104690265151215904174405777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139587020201621205565874369 104690265151215904174405777)
  ·
    refine ⟨78517698863411928130804333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104690265151215904174405777 78517698863411928130804333)
    ·
      refine ⟨29444137073779473049051625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78517698863411928130804333 29444137073779473049051625)
      ·
        refine ⟨22083102805334604786788719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29444137073779473049051625 22083102805334604786788719)
        ·
          refine ⟨33124654208001907180183079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22083102805334604786788719 33124654208001907180183079)
          ·
            refine ⟨49686981312002860770274619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33124654208001907180183079 49686981312002860770274619)
            ·
              refine ⟨74530471968004291155411929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49686981312002860770274619 74530471968004291155411929)
              ·
                refine ⟨55897853976003218366558947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74530471968004291155411929 55897853976003218366558947)
                ·
                  refine ⟨83846780964004827549838421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55897853976003218366558947 83846780964004827549838421)
                  ·
                    refine ⟨982579464421931572849669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83846780964004827549838421 982579464421931572849669)
                    ·
                      rfl

theorem cell23_5740700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_5740700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740700 prefixEnd_5740700 := by exact prefixLift 5740700
  have htrace : WordTrace (prefixWord ++ tailWord_5740700) baseStart_5740700 baseEnd_5740700 := by
    simpa [prefixWord, tailWord_5740700, baseEnd_5740700] using wordTrace_append hprefix tailTrace_5740700
  have hstable : (prefixWord ++ tailWord_5740700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740700).length < 2 ^ (prefixWord ++ tailWord_5740700).sum := by decide
  have hdescent : baseEnd_5740700 < baseStart_5740700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740717 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5740717 : Nat := 118140960795 + 5740717 * 2 ^ 59
def prefixEnd_5740717 : Nat := 4983230072969 + 3 ^ 40 * 5740717 * 2
def baseEnd_5740717 : Nat := 982582374145640384012143

theorem tailTrace_5740717 : CollatzResearch.WordTrace tailWord_5740717 prefixEnd_5740717 982582374145640384012143 := by
  unfold tailWord_5740717
  simp only [CollatzResearch.WordTrace]
  refine ⟨209381150343370220252180405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139587433562246813501453603 209381150343370220252180405)
  ·
    refine ⟨19629482844690958148641913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209381150343370220252180405 19629482844690958148641913)
    ·
      refine ⟨14722112133518218611481435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19629482844690958148641913 14722112133518218611481435)
      ·
        refine ⟨22083168200277327917222153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14722112133518218611481435 22083168200277327917222153)
        ·
          refine ⟨16562376150207995937916615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22083168200277327917222153 16562376150207995937916615)
          ·
            refine ⟨24843564225311993906874923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16562376150207995937916615 24843564225311993906874923)
            ·
              refine ⟨37265346337967990860312385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24843564225311993906874923 37265346337967990860312385)
              ·
                refine ⟨27949009753475993145234289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37265346337967990860312385 27949009753475993145234289)
                ·
                  refine ⟨20961757315106994858925717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27949009753475993145234289 20961757315106994858925717)
                  ·
                    refine ⟨982582374145640384012143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20961757315106994858925717 982582374145640384012143)
                    ·
                      rfl

theorem cell23_5740717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5740717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740717 prefixEnd_5740717 := by exact prefixLift 5740717
  have htrace : WordTrace (prefixWord ++ tailWord_5740717) baseStart_5740717 baseEnd_5740717 := by
    simpa [prefixWord, tailWord_5740717, baseEnd_5740717] using wordTrace_append hprefix tailTrace_5740717
  have hstable : (prefixWord ++ tailWord_5740717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740717).length < 2 ^ (prefixWord ++ tailWord_5740717).sum := by decide
  have hdescent : baseEnd_5740717 < baseStart_5740717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740718 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5740718 : Nat := 118140960795 + 5740718 * 2 ^ 59
def prefixEnd_5740718 : Nat := 4983230072969 + 3 ^ 40 * 5740718 * 2
def baseEnd_5740718 : Nat := 2947747635917575648123925

theorem tailTrace_5740718 : CollatzResearch.WordTrace tailWord_5740718 prefixEnd_5740718 2947747635917575648123925 := by
  unfold tailWord_5740718
  simp only [CollatzResearch.WordTrace]
  refine ⟨26172648352045824677870851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139587457877577731615311205 26172648352045824677870851)
  ·
    refine ⟨39258972528068737016806277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26172648352045824677870851 39258972528068737016806277)
    ·
      refine ⟨7361057349012888190651177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39258972528068737016806277 7361057349012888190651177)
      ·
        refine ⟨5520793011759666142988383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7361057349012888190651177 5520793011759666142988383)
        ·
          refine ⟨8281189517639499214482575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5520793011759666142988383 8281189517639499214482575)
          ·
            refine ⟨12421784276459248821723863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8281189517639499214482575 12421784276459248821723863)
            ·
              refine ⟨18632676414688873232585795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12421784276459248821723863 18632676414688873232585795)
              ·
                refine ⟨27949014622033309848878693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18632676414688873232585795 27949014622033309848878693)
                ·
                  refine ⟨5240440241631245596664755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27949014622033309848878693 5240440241631245596664755)
                  ·
                    refine ⟨7860660362446868394997133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5240440241631245596664755 7860660362446868394997133)
                    ·
                      refine ⟨2947747635917575648123925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7860660362446868394997133 2947747635917575648123925)
                      ·
                        rfl

theorem cell23_5740718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5740718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740718 prefixEnd_5740718 := by exact prefixLift 5740718
  have htrace : WordTrace (prefixWord ++ tailWord_5740718) baseStart_5740718 baseEnd_5740718 := by
    simpa [prefixWord, tailWord_5740718, baseEnd_5740718] using wordTrace_append hprefix tailTrace_5740718
  have hstable : (prefixWord ++ tailWord_5740718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740718).length < 2 ^ (prefixWord ++ tailWord_5740718).sum := by decide
  have hdescent : baseEnd_5740718 < baseStart_5740718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740730 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 7]
def baseStart_5740730 : Nat := 118140960795 + 5740730 * 2 ^ 59
def prefixEnd_5740730 : Nat := 4983230072969 + 3 ^ 40 * 5740730 * 2
def baseEnd_5740730 : Nat := 327528199742825511241541

theorem tailTrace_5740730 : CollatzResearch.WordTrace tailWord_5740730 prefixEnd_5740730 327528199742825511241541 := by
  unfold tailWord_5740730
  simp only [CollatzResearch.WordTrace]
  refine ⟨52345406123080780868100911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139587749661548748981602429 52345406123080780868100911)
  ·
    refine ⟨78518109184621171302151367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52345406123080780868100911 78518109184621171302151367)
    ·
      refine ⟨117777163776931756953227051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78518109184621171302151367 117777163776931756953227051)
      ·
        refine ⟨176665745665397635429840577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117777163776931756953227051 176665745665397635429840577)
        ·
          refine ⟨132499309249048226572380433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176665745665397635429840577 132499309249048226572380433)
          ·
            refine ⟨99374481936786169929285325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132499309249048226572380433 99374481936786169929285325)
            ·
              refine ⟨37265430726294813723481997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99374481936786169929285325 37265430726294813723481997)
              ·
                refine ⟨13974536522360555146305749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37265430726294813723481997 13974536522360555146305749)
                ·
                  refine ⟨327528199742825511241541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13974536522360555146305749 327528199742825511241541)
                  ·
                    rfl

theorem cell23_5740730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_5740730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740730 prefixEnd_5740730 := by exact prefixLift 5740730
  have htrace : WordTrace (prefixWord ++ tailWord_5740730) baseStart_5740730 baseEnd_5740730 := by
    simpa [prefixWord, tailWord_5740730, baseEnd_5740730] using wordTrace_append hprefix tailTrace_5740730
  have hstable : (prefixWord ++ tailWord_5740730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740730).length < 2 ^ (prefixWord ++ tailWord_5740730).sum := by decide
  have hdescent : baseEnd_5740730 < baseStart_5740730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740758 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5740758 : Nat := 118140960795 + 5740758 * 2 ^ 59
def prefixEnd_5740758 : Nat := 4983230072969 + 3 ^ 40 * 5740758 * 2
def baseEnd_5740758 : Nat := 2947768175143755491623741

theorem tailTrace_5740758 : CollatzResearch.WordTrace tailWord_5740758 prefixEnd_5740758 2947768175143755491623741 := by
  unfold tailWord_5740758
  simp only [CollatzResearch.WordTrace]
  refine ⟨13086415358513855265901433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139588430490814456169615285 13086415358513855265901433)
  ·
    refine ⟨9814811518885391449426075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13086415358513855265901433 9814811518885391449426075)
    ·
      refine ⟨14722217278328087174139113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9814811518885391449426075 14722217278328087174139113)
      ·
        refine ⟨11041662958746065380604335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14722217278328087174139113 11041662958746065380604335)
        ·
          refine ⟨16562494438119098070906503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11041662958746065380604335 16562494438119098070906503)
          ·
            refine ⟨24843741657178647106359755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16562494438119098070906503 24843741657178647106359755)
            ·
              refine ⟨37265612485767970659539633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24843741657178647106359755 37265612485767970659539633)
              ·
                refine ⟨27949209364325977994654725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37265612485767970659539633 27949209364325977994654725)
                ·
                  refine ⟨5240476755811120873997761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27949209364325977994654725 5240476755811120873997761)
                  ·
                    refine ⟨3930357566858340655498321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240476755811120873997761 3930357566858340655498321)
                    ·
                      refine ⟨2947768175143755491623741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930357566858340655498321 2947768175143755491623741)
                      ·
                        rfl

theorem cell23_5740758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5740758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740758 prefixEnd_5740758 := by exact prefixLift 5740758
  have htrace : WordTrace (prefixWord ++ tailWord_5740758) baseStart_5740758 baseEnd_5740758 := by
    simpa [prefixWord, tailWord_5740758, baseEnd_5740758] using wordTrace_append hprefix tailTrace_5740758
  have hstable : (prefixWord ++ tailWord_5740758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740758).length < 2 ^ (prefixWord ++ tailWord_5740758).sum := by decide
  have hdescent : baseEnd_5740758 < baseStart_5740758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740767 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 7, 2]
def baseStart_5740767 : Nat := 118140960795 + 5740767 * 2 ^ 59
def prefixEnd_5740767 : Nat := 4983230072969 + 3 ^ 40 * 5740767 * 2
def baseEnd_5740767 : Nat := 2947772796469645956411199

theorem tailTrace_5740767 : CollatzResearch.WordTrace tailWord_5740767 prefixEnd_5740767 2947772796469645956411199 := by
  unfold tailWord_5740767
  simp only [CollatzResearch.WordTrace]
  refine ⟨209382973993189078791500555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139588649328792719194333703 209382973993189078791500555)
  ·
    refine ⟨314074460989783618187250833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209382973993189078791500555 314074460989783618187250833)
    ·
      refine ⟨235555845742337713640438125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314074460989783618187250833 235555845742337713640438125)
      ·
        refine ⟨88333442153376642615164297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235555845742337713640438125 88333442153376642615164297)
        ·
          refine ⟨66250081615032481961373223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88333442153376642615164297 66250081615032481961373223)
          ·
            refine ⟨99375122422548722942059835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66250081615032481961373223 99375122422548722942059835)
            ·
              refine ⟨149062683633823084413089753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99375122422548722942059835 149062683633823084413089753)
              ·
                refine ⟨111797012725367313309817315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149062683633823084413089753 111797012725367313309817315)
                ·
                  refine ⟨167695519088050969964725973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111797012725367313309817315 167695519088050969964725973)
                  ·
                    refine ⟨3930363728626194608548265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167695519088050969964725973 3930363728626194608548265)
                    ·
                      refine ⟨2947772796469645956411199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930363728626194608548265 2947772796469645956411199)
                      ·
                        rfl

theorem cell23_5740767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_5740767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740767 prefixEnd_5740767 := by exact prefixLift 5740767
  have htrace : WordTrace (prefixWord ++ tailWord_5740767) baseStart_5740767 baseEnd_5740767 := by
    simpa [prefixWord, tailWord_5740767, baseEnd_5740767] using wordTrace_append hprefix tailTrace_5740767
  have hstable : (prefixWord ++ tailWord_5740767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740767).length < 2 ^ (prefixWord ++ tailWord_5740767).sum := by decide
  have hdescent : baseEnd_5740767 < baseStart_5740767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740781 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 7]
def baseStart_5740781 : Nat := 118140960795 + 5740781 * 2 ^ 59
def prefixEnd_5740781 : Nat := 4983230072969 + 3 ^ 40 * 5740781 * 2
def baseEnd_5740781 : Nat := 327531109466534322404015

theorem tailTrace_5740781 : CollatzResearch.WordTrace tailWord_5740781 prefixEnd_5740781 327531109466534322404015 := by
  unfold tailWord_5740781
  simp only [CollatzResearch.WordTrace]
  refine ⟨209383484615138359182510197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139588989743425572788340131 209383484615138359182510197)
  ·
    refine ⟨19629701682669221173360331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209383484615138359182510197 19629701682669221173360331)
    ·
      refine ⟨29444552524003831760040497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19629701682669221173360331 29444552524003831760040497)
      ·
        refine ⟨22083414393002873820030373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29444552524003831760040497 22083414393002873820030373)
        ·
          refine ⟨4140640198688038841255695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22083414393002873820030373 4140640198688038841255695)
          ·
            refine ⟨6210960298032058261883543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140640198688038841255695 6210960298032058261883543)
            ·
              refine ⟨9316440447048087392825315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6210960298032058261883543 9316440447048087392825315)
              ·
                refine ⟨13974660670572131089237973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9316440447048087392825315 13974660670572131089237973)
                ·
                  refine ⟨327531109466534322404015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13974660670572131089237973 327531109466534322404015)
                  ·
                    rfl

theorem cell23_5740781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_5740781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740781 prefixEnd_5740781 := by exact prefixLift 5740781
  have htrace : WordTrace (prefixWord ++ tailWord_5740781) baseStart_5740781 baseEnd_5740781 := by
    simpa [prefixWord, tailWord_5740781, baseEnd_5740781] using wordTrace_append hprefix tailTrace_5740781
  have hstable : (prefixWord ++ tailWord_5740781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740781).length < 2 ^ (prefixWord ++ tailWord_5740781).sum := by decide
  have hdescent : baseEnd_5740781 < baseStart_5740781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740814 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_5740814 : Nat := 118140960795 + 5740814 * 2 ^ 59
def prefixEnd_5740814 : Nat := 4983230072969 + 3 ^ 40 * 5740814 * 2
def baseEnd_5740814 : Nat := 2947796930060407272523483

theorem tailTrace_5740814 : CollatzResearch.WordTrace tailWord_5740814 prefixEnd_5740814 2947796930060407272523483 := by
  unfold tailWord_5740814
  simp only [CollatzResearch.WordTrace]
  refine ⟨26173086028002350727307687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139589792149345870545640997 26173086028002350727307687)
  ·
    refine ⟨39259629042003526090961531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26173086028002350727307687 39259629042003526090961531)
    ·
      refine ⟨58889443563005289136442297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39259629042003526090961531 58889443563005289136442297)
      ·
        refine ⟨44167082672253966852331723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58889443563005289136442297 44167082672253966852331723)
        ·
          refine ⟨66250624008380950278497585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44167082672253966852331723 66250624008380950278497585)
          ·
            refine ⟨49687968006285712708873189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66250624008380950278497585 49687968006285712708873189)
            ·
              refine ⟨9316494001178571132913723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49687968006285712708873189 9316494001178571132913723)
              ·
                refine ⟨13974741001767856699370585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9316494001178571132913723 13974741001767856699370585)
                ·
                  refine ⟨10481055751325892524527939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13974741001767856699370585 10481055751325892524527939)
                  ·
                    refine ⟨15721583626988838786791909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10481055751325892524527939 15721583626988838786791909)
                    ·
                      refine ⟨2947796930060407272523483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15721583626988838786791909 2947796930060407272523483)
                      ·
                        rfl

theorem cell23_5740814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_5740814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740814 prefixEnd_5740814 := by exact prefixLift 5740814
  have htrace : WordTrace (prefixWord ++ tailWord_5740814) baseStart_5740814 baseEnd_5740814 := by
    simpa [prefixWord, tailWord_5740814, baseEnd_5740814] using wordTrace_append hprefix tailTrace_5740814
  have hstable : (prefixWord ++ tailWord_5740814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740814).length < 2 ^ (prefixWord ++ tailWord_5740814).sum := by decide
  have hdescent : baseEnd_5740814 < baseStart_5740814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740867 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 3, 5]
def baseStart_5740867 : Nat := 118140960795 + 5740867 * 2 ^ 59
def prefixEnd_5740867 : Nat := 4983230072969 + 3 ^ 40 * 5740867 * 2
def baseEnd_5740867 : Nat := 982608048178365188386913

theorem tailTrace_5740867 : CollatzResearch.WordTrace tailWord_5740867 prefixEnd_5740867 982608048178365188386913 := by
  unfold tailWord_5740867
  simp only [CollatzResearch.WordTrace]
  refine ⟨209386621292826795870140855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139591080861884530580093903 209386621292826795870140855)
  ·
    refine ⟨314079931939240193805211283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209386621292826795870140855 314079931939240193805211283)
    ·
      refine ⟨471119897908860290707816925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314079931939240193805211283 471119897908860290707816925)
      ·
        refine ⟨176669961715822609015431347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 471119897908860290707816925 176669961715822609015431347)
        ·
          refine ⟨265004942573733913523147021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176669961715822609015431347 265004942573733913523147021)
          ·
            refine ⟨99376853465150217571180133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265004942573733913523147021 99376853465150217571180133)
            ·
              refine ⟨18633160024715665794596275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99376853465150217571180133 18633160024715665794596275)
              ·
                refine ⟨27949740037073498691894413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18633160024715665794596275 27949740037073498691894413)
                ·
                  refine ⟨10481152513902562009460405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27949740037073498691894413 10481152513902562009460405)
                  ·
                    refine ⟨982608048178365188386913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10481152513902562009460405 982608048178365188386913)
                    ·
                      rfl

theorem cell23_5740867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 5].length) (baseStart_5740867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740867 prefixEnd_5740867 := by exact prefixLift 5740867
  have htrace : WordTrace (prefixWord ++ tailWord_5740867) baseStart_5740867 baseEnd_5740867 := by
    simpa [prefixWord, tailWord_5740867, baseEnd_5740867] using wordTrace_append hprefix tailTrace_5740867
  have hstable : (prefixWord ++ tailWord_5740867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740867).length < 2 ^ (prefixWord ++ tailWord_5740867).sum := by decide
  have hdescent : baseEnd_5740867 < baseStart_5740867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740898 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_5740898 : Nat := 118140960795 + 5740898 * 2 ^ 59
def prefixEnd_5740898 : Nat := 4983230072969 + 3 ^ 40 * 5740898 * 2
def baseEnd_5740898 : Nat := 2947840062435384943873097

theorem tailTrace_5740898 : CollatzResearch.WordTrace tailWord_5740898 prefixEnd_5740898 2947840062435384943873097 := by
  unfold tailWord_5740898
  simp only [CollatzResearch.WordTrace]
  refine ⟨52346937988928622041129837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139591834637142992109679565 52346937988928622041129837)
  ·
    refine ⟨19630101745848233265423689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52346937988928622041129837 19630101745848233265423689)
    ·
      refine ⟨14722576309386174949067767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19630101745848233265423689 14722576309386174949067767)
      ·
        refine ⟨22083864464079262423601651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14722576309386174949067767 22083864464079262423601651)
        ·
          refine ⟨33125796696118893635402477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22083864464079262423601651 33125796696118893635402477)
          ·
            refine ⟨12422173761044585113275929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33125796696118893635402477 12422173761044585113275929)
            ·
              refine ⟨9316630320783438834956947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12422173761044585113275929 9316630320783438834956947)
              ·
                refine ⟨13974945481175158252435421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9316630320783438834956947 13974945481175158252435421)
                ·
                  refine ⟨5240604555440684344663283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13974945481175158252435421 5240604555440684344663283)
                  ·
                    refine ⟨7860906833161026516994925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5240604555440684344663283 7860906833161026516994925)
                    ·
                      refine ⟨2947840062435384943873097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7860906833161026516994925 2947840062435384943873097)
                      ·
                        rfl

theorem cell23_5740898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_5740898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740898 prefixEnd_5740898 := by exact prefixLift 5740898
  have htrace : WordTrace (prefixWord ++ tailWord_5740898) baseStart_5740898 baseEnd_5740898 := by
    simpa [prefixWord, tailWord_5740898, baseEnd_5740898] using wordTrace_append hprefix tailTrace_5740898
  have hstable : (prefixWord ++ tailWord_5740898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740898).length < 2 ^ (prefixWord ++ tailWord_5740898).sum := by decide
  have hdescent : baseEnd_5740898 < baseStart_5740898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740907 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5]
def baseStart_5740907 : Nat := 118140960795 + 5740907 * 2 ^ 59
def prefixEnd_5740907 : Nat := 4983230072969 + 3 ^ 40 * 5740907 * 2
def baseEnd_5740907 : Nat := 2947844683761275408660555

theorem tailTrace_5740907 : CollatzResearch.WordTrace tailWord_5740907 prefixEnd_5740907 2947844683761275408660555 := by
  unfold tailWord_5740907
  simp only [CollatzResearch.WordTrace]
  refine ⟨209388080212681882701596975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139592053475121255134397983 209388080212681882701596975)
  ·
    refine ⟨314082120319022824052395463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209388080212681882701596975 314082120319022824052395463)
    ·
      refine ⟨471123180478534236078593195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314082120319022824052395463 471123180478534236078593195)
      ·
        refine ⟨706684770717801354117889793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471123180478534236078593195 706684770717801354117889793)
        ·
          refine ⟨530013578038351015588417345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706684770717801354117889793 530013578038351015588417345)
          ·
            refine ⟨397510183528763261691313009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530013578038351015588417345 397510183528763261691313009)
            ·
              refine ⟨298132637646572446268484757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397510183528763261691313009 298132637646572446268484757)
              ·
                refine ⟨13974967389683083418835223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 298132637646572446268484757 13974967389683083418835223)
                ·
                  refine ⟨20962451084524625128252835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13974967389683083418835223 20962451084524625128252835)
                  ·
                    refine ⟨31443676626786937692379253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20962451084524625128252835 31443676626786937692379253)
                    ·
                      refine ⟨2947844683761275408660555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31443676626786937692379253 2947844683761275408660555)
                      ·
                        rfl

theorem cell23_5740907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5].length) (baseStart_5740907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740907 prefixEnd_5740907 := by exact prefixLift 5740907
  have htrace : WordTrace (prefixWord ++ tailWord_5740907) baseStart_5740907 baseEnd_5740907 := by
    simpa [prefixWord, tailWord_5740907, baseEnd_5740907] using wordTrace_append hprefix tailTrace_5740907
  have hstable : (prefixWord ++ tailWord_5740907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740907).length < 2 ^ (prefixWord ++ tailWord_5740907).sum := by decide
  have hdescent : baseEnd_5740907 < baseStart_5740907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740914 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_5740914 : Nat := 118140960795 + 5740914 * 2 ^ 59
def prefixEnd_5740914 : Nat := 4983230072969 + 3 ^ 40 * 5740914 * 2
def baseEnd_5740914 : Nat := 982616092708618960424341

theorem tailTrace_5740914 : CollatzResearch.WordTrace tailWord_5740914 prefixEnd_5740914 982616092708618960424341 := by
  unfold tailWord_5740914
  simp only [CollatzResearch.WordTrace]
  refine ⟨52347083880914130724275449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139592223682437681931401197 52347083880914130724275449)
  ·
    refine ⟨39260312910685598043206587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52347083880914130724275449 39260312910685598043206587)
    ·
      refine ⟨58890469366028397064809881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39260312910685598043206587 58890469366028397064809881)
      ·
        refine ⟨44167852024521297798607411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58890469366028397064809881 44167852024521297798607411)
        ·
          refine ⟨66251778036781946697911117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44167852024521297798607411 66251778036781946697911117)
          ·
            refine ⟨24844416763793230011716669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66251778036781946697911117 24844416763793230011716669)
            ·
              refine ⟨9316656286422461254393751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24844416763793230011716669 9316656286422461254393751)
              ·
                refine ⟨13974984429633691881590627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9316656286422461254393751 13974984429633691881590627)
                ·
                  refine ⟨20962476644450537822385941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13974984429633691881590627 20962476644450537822385941)
                  ·
                    refine ⟨982616092708618960424341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20962476644450537822385941 982616092708618960424341)
                    ·
                      rfl

theorem cell23_5740914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_5740914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740914 prefixEnd_5740914 := by exact prefixLift 5740914
  have htrace : WordTrace (prefixWord ++ tailWord_5740914) baseStart_5740914 baseEnd_5740914 := by
    simpa [prefixWord, tailWord_5740914, baseEnd_5740914] using wordTrace_append hprefix tailTrace_5740914
  have hstable : (prefixWord ++ tailWord_5740914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740914).length < 2 ^ (prefixWord ++ tailWord_5740914).sum := by decide
  have hdescent : baseEnd_5740914 < baseStart_5740914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5740961 : List Nat := [1, 2, 3, 5, 1, 1, 2, 8]
def baseStart_5740961 : Nat := 118140960795 + 5740961 * 2 ^ 59
def prefixEnd_5740961 : Nat := 4983230072969 + 3 ^ 40 * 5740961 * 2
def baseEnd_5740961 : Nat := 109180459693208081384641

theorem tailTrace_5740961 : CollatzResearch.WordTrace tailWord_5740961 prefixEnd_5740961 109180459693208081384641 := by
  unfold tailWord_5740961
  simp only [CollatzResearch.WordTrace]
  refine ⟨209390049754486249924062737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139593366502990833282708491 209390049754486249924062737)
  ·
    refine ⟨157042537315864687443047053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209390049754486249924062737 157042537315864687443047053)
    ·
      refine ⟨58890951493449257791142645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157042537315864687443047053 58890951493449257791142645)
      ·
        refine ⟨5521026702510867917919623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58890951493449257791142645 5521026702510867917919623)
        ·
          refine ⟨8281540053766301876879435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521026702510867917919623 8281540053766301876879435)
          ·
            refine ⟨12422310080649452815319153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8281540053766301876879435 12422310080649452815319153)
            ·
              refine ⟨9316732560487089611489365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12422310080649452815319153 9316732560487089611489365)
              ·
                refine ⟨109180459693208081384641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9316732560487089611489365 109180459693208081384641)
                ·
                  rfl

theorem cell23_5740961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 8].length) (baseStart_5740961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5740961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5740961 prefixEnd_5740961 := by exact prefixLift 5740961
  have htrace : WordTrace (prefixWord ++ tailWord_5740961) baseStart_5740961 baseEnd_5740961 := by
    simpa [prefixWord, tailWord_5740961, baseEnd_5740961] using wordTrace_append hprefix tailTrace_5740961
  have hstable : (prefixWord ++ tailWord_5740961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5740961).length < 2 ^ (prefixWord ++ tailWord_5740961).sum := by decide
  have hdescent : baseEnd_5740961 < baseStart_5740961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5740961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741007 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_5741007 : Nat := 118140960795 + 5741007 * 2 ^ 59
def prefixEnd_5741007 : Nat := 4983230072969 + 3 ^ 40 * 5741007 * 2
def baseEnd_5741007 : Nat := 2947896031826725017410095

theorem tailTrace_5741007 : CollatzResearch.WordTrace tailWord_5741007 prefixEnd_5741007 2947896031826725017410095 := by
  unfold tailWord_5741007
  simp only [CollatzResearch.WordTrace]
  refine ⟨209391727512319599780237275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139594485008213066520158183 209391727512319599780237275)
  ·
    refine ⟨314087591268479399670355913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209391727512319599780237275 314087591268479399670355913)
    ·
      refine ⟨235565693451359549752766935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314087591268479399670355913 235565693451359549752766935)
      ·
        refine ⟨353348540177039324629150403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235565693451359549752766935 353348540177039324629150403)
        ·
          refine ⟨530022810265558986943725605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353348540177039324629150403 530022810265558986943725605)
          ·
            refine ⟨99379276924792310051948551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 530022810265558986943725605 99379276924792310051948551)
            ·
              refine ⟨149068915387188465077922827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99379276924792310051948551 149068915387188465077922827)
              ·
                refine ⟨223603373080782697616884241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149068915387188465077922827 223603373080782697616884241)
                ·
                  refine ⟨167702529810587023212663181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223603373080782697616884241 167702529810587023212663181)
                  ·
                    refine ⟨62888448678970133704748693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167702529810587023212663181 62888448678970133704748693)
                    ·
                      refine ⟨2947896031826725017410095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62888448678970133704748693 2947896031826725017410095)
                      ·
                        rfl

theorem cell23_5741007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_5741007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741007 prefixEnd_5741007 := by exact prefixLift 5741007
  have htrace : WordTrace (prefixWord ++ tailWord_5741007) baseStart_5741007 baseEnd_5741007 := by
    simpa [prefixWord, tailWord_5741007, baseEnd_5741007] using wordTrace_append hprefix tailTrace_5741007
  have hstable : (prefixWord ++ tailWord_5741007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741007).length < 2 ^ (prefixWord ++ tailWord_5741007).sum := by decide
  have hdescent : baseEnd_5741007 < baseStart_5741007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741011 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 10, 2, 2]
def baseStart_5741011 : Nat := 118140960795 + 5741011 * 2 ^ 59
def prefixEnd_5741011 : Nat := 4983230072969 + 3 ^ 40 * 5741011 * 2
def baseEnd_5741011 : Nat := 2947898085749343001760077

theorem tailTrace_5741011 : CollatzResearch.WordTrace tailWord_5741011 prefixEnd_5741011 2947898085749343001760077 := by
  unfold tailWord_5741011
  simp only [CollatzResearch.WordTrace]
  refine ⟨209391873404305108463382887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139594582269536738975588591 209391873404305108463382887)
  ·
    refine ⟨314087810106457662695074331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209391873404305108463382887 314087810106457662695074331)
    ·
      refine ⟨471131715159686494042611497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314087810106457662695074331 471131715159686494042611497)
      ·
        refine ⟨353348786369764870531958623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471131715159686494042611497 353348786369764870531958623)
        ·
          refine ⟨530023179554647305797937935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353348786369764870531958623 530023179554647305797937935)
          ·
            refine ⟨795034769331970958696906903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530023179554647305797937935 795034769331970958696906903)
            ·
              refine ⟨1192552153997956438045360355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795034769331970958696906903 1192552153997956438045360355)
              ·
                refine ⟨1788828230996934657068040533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192552153997956438045360355 1788828230996934657068040533)
                ·
                  refine ⟨5240707707998832003129025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1788828230996934657068040533 5240707707998832003129025)
                  ·
                    refine ⟨3930530780999124002346769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240707707998832003129025 3930530780999124002346769)
                    ·
                      refine ⟨2947898085749343001760077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930530780999124002346769 2947898085749343001760077)
                      ·
                        rfl

theorem cell23_5741011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 2, 2].length) (baseStart_5741011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741011 prefixEnd_5741011 := by exact prefixLift 5741011
  have htrace : WordTrace (prefixWord ++ tailWord_5741011) baseStart_5741011 baseEnd_5741011 := by
    simpa [prefixWord, tailWord_5741011, baseEnd_5741011] using wordTrace_append hprefix tailTrace_5741011
  have hstable : (prefixWord ++ tailWord_5741011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741011).length < 2 ^ (prefixWord ++ tailWord_5741011).sum := by decide
  have hdescent : baseEnd_5741011 < baseStart_5741011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741024 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4]
def baseStart_5741024 : Nat := 118140960795 + 5741024 * 2 ^ 59
def prefixEnd_5741024 : Nat := 4983230072969 + 3 ^ 40 * 5741024 * 2
def baseEnd_5741024 : Nat := 2947904760997851450897517

theorem tailTrace_5741024 : CollatzResearch.WordTrace tailWord_5741024 prefixEnd_5741024 2947904760997851450897517 := by
  unfold tailWord_5741024
  simp only [CollatzResearch.WordTrace]
  refine ⟨104696173776629005841803063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139594898368838674455737417 104696173776629005841803063)
  ·
    refine ⟨157044260664943508762704595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104696173776629005841803063 157044260664943508762704595)
    ·
      refine ⟨235566390997415263144056893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157044260664943508762704595 235566390997415263144056893)
      ·
        refine ⟨88337396624030723679021335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235566390997415263144056893 88337396624030723679021335)
        ·
          refine ⟨132506094936046085518532003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88337396624030723679021335 132506094936046085518532003)
          ·
            refine ⟨198759142404069128277798005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132506094936046085518532003 198759142404069128277798005)
            ·
              refine ⟨18633669600381480776043563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198759142404069128277798005 18633669600381480776043563)
              ·
                refine ⟨27950504400572221164065345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18633669600381480776043563 27950504400572221164065345)
                ·
                  refine ⟨20962878300429165873049009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27950504400572221164065345 20962878300429165873049009)
                  ·
                    refine ⟨15722158725321874404786757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20962878300429165873049009 15722158725321874404786757)
                    ·
                      refine ⟨2947904760997851450897517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15722158725321874404786757 2947904760997851450897517)
                      ·
                        rfl

theorem cell23_5741024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_5741024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741024 prefixEnd_5741024 := by exact prefixLift 5741024
  have htrace : WordTrace (prefixWord ++ tailWord_5741024) baseStart_5741024 baseEnd_5741024 := by
    simpa [prefixWord, tailWord_5741024, baseEnd_5741024] using wordTrace_append hprefix tailTrace_5741024
  have hstable : (prefixWord ++ tailWord_5741024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741024).length < 2 ^ (prefixWord ++ tailWord_5741024).sum := by decide
  have hdescent : baseEnd_5741024 < baseStart_5741024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741034 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 9]
def baseStart_5741034 : Nat := 118140960795 + 5741034 * 2 ^ 59
def prefixEnd_5741034 : Nat := 4983230072969 + 3 ^ 40 * 5741034 * 2
def baseEnd_5741034 : Nat := 327545543978266267974719

theorem tailTrace_5741034 : CollatzResearch.WordTrace tailWord_5741034 prefixEnd_5741034 327545543978266267974719 := by
  unfold tailWord_5741034
  simp only [CollatzResearch.WordTrace]
  refine ⟨52348178070805445847867539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139595141522147855594313437 52348178070805445847867539)
  ·
    refine ⟨78522267106208168771801309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52348178070805445847867539 78522267106208168771801309)
    ·
      refine ⟨29445850164828063289425491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78522267106208168771801309 29445850164828063289425491)
      ·
        refine ⟨44168775247242094934138237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29445850164828063289425491 44168775247242094934138237)
        ·
          refine ⟨16563290717715785600301839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44168775247242094934138237 16563290717715785600301839)
          ·
            refine ⟨24844936076573678400452759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16563290717715785600301839 24844936076573678400452759)
            ·
              refine ⟨37267404114860517600679139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24844936076573678400452759 37267404114860517600679139)
              ·
                refine ⟨55901106172290776401018709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37267404114860517600679139 55901106172290776401018709)
                ·
                  refine ⟨327545543978266267974719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55901106172290776401018709 327545543978266267974719)
                  ·
                    rfl

theorem cell23_5741034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_5741034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741034 prefixEnd_5741034 := by exact prefixLift 5741034
  have htrace : WordTrace (prefixWord ++ tailWord_5741034) baseStart_5741034 baseEnd_5741034 := by
    simpa [prefixWord, tailWord_5741034, baseEnd_5741034] using wordTrace_append hprefix tailTrace_5741034
  have hstable : (prefixWord ++ tailWord_5741034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741034).length < 2 ^ (prefixWord ++ tailWord_5741034).sum := by decide
  have hdescent : baseEnd_5741034 < baseStart_5741034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741064 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 4, 5]
def baseStart_5741064 : Nat := 118140960795 + 5741064 * 2 ^ 59
def prefixEnd_5741064 : Nat := 4983230072969 + 3 ^ 40 * 5741064 * 2
def baseEnd_5741064 : Nat := 982641766741343764799111

theorem tailTrace_5741064 : CollatzResearch.WordTrace tailWord_5741064 prefixEnd_5741064 982641766741343764799111 := by
  unfold tailWord_5741064
  simp only [CollatzResearch.WordTrace]
  refine ⟨104696903236556549257531123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139595870982075399010041497 104696903236556549257531123)
  ·
    refine ⟨157045354854834823886296685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104696903236556549257531123 157045354854834823886296685)
    ·
      refine ⟨58892008070563058957361257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157045354854834823886296685 58892008070563058957361257)
      ·
        refine ⟨44169006052922294218020943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58892008070563058957361257 44169006052922294218020943)
        ·
          refine ⟨66253509079383441327031415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44169006052922294218020943 66253509079383441327031415)
          ·
            refine ⟨99380263619075161990547123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66253509079383441327031415 99380263619075161990547123)
            ·
              refine ⟨149070395428612742985820685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99380263619075161990547123 149070395428612742985820685)
              ·
                refine ⟨55901398285729778619682757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149070395428612742985820685 55901398285729778619682757)
                ·
                  refine ⟨10481512178574333491190517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55901398285729778619682757 10481512178574333491190517)
                  ·
                    refine ⟨982641766741343764799111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10481512178574333491190517 982641766741343764799111)
                    ·
                      rfl

theorem cell23_5741064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_5741064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741064 prefixEnd_5741064 := by exact prefixLift 5741064
  have htrace : WordTrace (prefixWord ++ tailWord_5741064) baseStart_5741064 baseEnd_5741064 := by
    simpa [prefixWord, tailWord_5741064, baseEnd_5741064] using wordTrace_append hprefix tailTrace_5741064
  have hstable : (prefixWord ++ tailWord_5741064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741064).length < 2 ^ (prefixWord ++ tailWord_5741064).sum := by decide
  have hdescent : baseEnd_5741064 < baseStart_5741064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741079 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5741079 : Nat := 118140960795 + 5741079 * 2 ^ 59
def prefixEnd_5741079 : Nat := 4983230072969 + 3 ^ 40 * 5741079 * 2
def baseEnd_5741079 : Nat := 2947933002433848735709765

theorem tailTrace_5741079 : CollatzResearch.WordTrace tailWord_5741079 prefixEnd_5741079 2947933002433848735709765 := by
  unfold tailWord_5741079
  simp only [CollatzResearch.WordTrace]
  refine ⟨209394353568058756076858291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139596235712039170717905527 209394353568058756076858291)
  ·
    refine ⟨314091530352088134115287437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209394353568058756076858291 314091530352088134115287437)
    ·
      refine ⟨117784323882033050293232789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314091530352088134115287437 117784323882033050293232789)
      ·
        refine ⟨5521140181970299232495287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117784323882033050293232789 5521140181970299232495287)
        ·
          refine ⟨8281710272955448848742931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521140181970299232495287 8281710272955448848742931)
          ·
            refine ⟨12422565409433173273114397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8281710272955448848742931 12422565409433173273114397)
            ·
              refine ⟨4658462028537439977417899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12422565409433173273114397 4658462028537439977417899)
              ·
                refine ⟨6987693042806159966126849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658462028537439977417899 6987693042806159966126849)
                ·
                  refine ⟨5240769782104619974595137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6987693042806159966126849 5240769782104619974595137)
                  ·
                    refine ⟨3930577336578464980946353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240769782104619974595137 3930577336578464980946353)
                    ·
                      refine ⟨2947933002433848735709765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930577336578464980946353 2947933002433848735709765)
                      ·
                        rfl

theorem cell23_5741079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5741079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741079 prefixEnd_5741079 := by exact prefixLift 5741079
  have htrace : WordTrace (prefixWord ++ tailWord_5741079) baseStart_5741079 baseEnd_5741079 := by
    simpa [prefixWord, tailWord_5741079, baseEnd_5741079] using wordTrace_append hprefix tailTrace_5741079
  have hstable : (prefixWord ++ tailWord_5741079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741079).length < 2 ^ (prefixWord ++ tailWord_5741079).sum := by decide
  have hdescent : baseEnd_5741079 < baseStart_5741079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741102 : List Nat := [4, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_5741102 : Nat := 118140960795 + 5741102 * 2 ^ 59
def prefixEnd_5741102 : Nat := 4983230072969 + 3 ^ 40 * 5741102 * 2
def baseEnd_5741102 : Nat := 327549423609878016191351

theorem tailTrace_5741102 : CollatzResearch.WordTrace tailWord_5741102 prefixEnd_5741102 327549423609878016191351 := by
  unfold tailWord_5741102
  simp only [CollatzResearch.WordTrace]
  refine ⟨26174399055871928875618195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139596794964650287336630373 26174399055871928875618195)
  ·
    refine ⟨39261598583807893313427293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26174399055871928875618195 39261598583807893313427293)
    ·
      refine ⟨14723099468927959992535235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39261598583807893313427293 14723099468927959992535235)
      ·
        refine ⟨22084649203391939988802853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14723099468927959992535235 22084649203391939988802853)
        ·
          refine ⟨4140871725635988747900535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22084649203391939988802853 4140871725635988747900535)
          ·
            refine ⟨6211307588453983121850803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4140871725635988747900535 6211307588453983121850803)
            ·
              refine ⟨9316961382680974682776205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211307588453983121850803 9316961382680974682776205)
              ·
                refine ⟨3493860518505365506041077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9316961382680974682776205 3493860518505365506041077)
                ·
                  refine ⟨327549423609878016191351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3493860518505365506041077 327549423609878016191351)
                  ·
                    rfl

theorem cell23_5741102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_5741102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741102 prefixEnd_5741102 := by exact prefixLift 5741102
  have htrace : WordTrace (prefixWord ++ tailWord_5741102) baseStart_5741102 baseEnd_5741102 := by
    simpa [prefixWord, tailWord_5741102, baseEnd_5741102] using wordTrace_append hprefix tailTrace_5741102
  have hstable : (prefixWord ++ tailWord_5741102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741102).length < 2 ^ (prefixWord ++ tailWord_5741102).sum := by decide
  have hdescent : baseEnd_5741102 < baseStart_5741102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741128 : List Nat := [2, 1, 3, 1, 1, 1, 1, 8, 1, 4]
def baseStart_5741128 : Nat := 118140960795 + 5741128 * 2 ^ 59
def prefixEnd_5741128 : Nat := 4983230072969 + 3 ^ 40 * 5741128 * 2
def baseEnd_5741128 : Nat := 982652720995306347999013

theorem tailTrace_5741128 : CollatzResearch.WordTrace tailWord_5741128 prefixEnd_5741128 982652720995306347999013 := by
  unfold tailWord_5741128
  simp only [CollatzResearch.WordTrace]
  refine ⟨104698070372440618722696019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139597427163254158296928025 104698070372440618722696019)
  ·
    refine ⟨157047105558660928084044029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104698070372440618722696019 157047105558660928084044029)
    ·
      refine ⟨58892664584497848031516511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157047105558660928084044029 58892664584497848031516511)
      ·
        refine ⟨88338996876746772047274767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58892664584497848031516511 88338996876746772047274767)
        ·
          refine ⟨132508495315120158070912151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88338996876746772047274767 132508495315120158070912151)
          ·
            refine ⟨198762742972680237106368227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132508495315120158070912151 198762742972680237106368227)
            ·
              refine ⟨298144114459020355659552341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198762742972680237106368227 298144114459020355659552341)
              ·
                refine ⟨3493876341316644792885379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 298144114459020355659552341 3493876341316644792885379)
                ·
                  refine ⟨5240814511974967189328069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493876341316644792885379 5240814511974967189328069)
                  ·
                    refine ⟨982652720995306347999013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5240814511974967189328069 982652720995306347999013)
                    ·
                      rfl

theorem cell23_5741128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_5741128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741128 prefixEnd_5741128 := by exact prefixLift 5741128
  have htrace : WordTrace (prefixWord ++ tailWord_5741128) baseStart_5741128 baseEnd_5741128 := by
    simpa [prefixWord, tailWord_5741128, baseEnd_5741128] using wordTrace_append hprefix tailTrace_5741128
  have hstable : (prefixWord ++ tailWord_5741128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741128).length < 2 ^ (prefixWord ++ tailWord_5741128).sum := by decide
  have hdescent : baseEnd_5741128 < baseStart_5741128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741144 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_5741144 : Nat := 118140960795 + 5741144 * 2 ^ 59
def prefixEnd_5741144 : Nat := 4983230072969 + 3 ^ 40 * 5741144 * 2
def baseEnd_5741144 : Nat := 2947966378676390981396965

theorem tailTrace_5741144 : CollatzResearch.WordTrace tailWord_5741144 prefixEnd_5741144 2947966378676390981396965 := by
  unfold tailWord_5741144
  simp only [CollatzResearch.WordTrace]
  refine ⟨104698362156411636088987243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139597816208548848118649657 104698362156411636088987243)
  ·
    refine ⟨157047543234617454133480865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104698362156411636088987243 157047543234617454133480865)
    ·
      refine ⟨117785657425963090600110649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157047543234617454133480865 117785657425963090600110649)
      ·
        refine ⟨88339243069472317950082987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117785657425963090600110649 88339243069472317950082987)
        ·
          refine ⟨132508864604208476925124481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88339243069472317950082987 132508864604208476925124481)
          ·
            refine ⟨99381648453156357693843361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132508864604208476925124481 99381648453156357693843361)
            ·
              refine ⟨74536236339867268270382521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99381648453156357693843361 74536236339867268270382521)
              ·
                refine ⟨55902177254900451202786891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74536236339867268270382521 55902177254900451202786891)
                ·
                  refine ⟨83853265882350676804180337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55902177254900451202786891 83853265882350676804180337)
                  ·
                    refine ⟨62889949411763007603135253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83853265882350676804180337 62889949411763007603135253)
                    ·
                      refine ⟨2947966378676390981396965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62889949411763007603135253 2947966378676390981396965)
                      ·
                        rfl

theorem cell23_5741144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_5741144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741144 prefixEnd_5741144 := by exact prefixLift 5741144
  have htrace : WordTrace (prefixWord ++ tailWord_5741144) baseStart_5741144 baseEnd_5741144 := by
    simpa [prefixWord, tailWord_5741144, baseEnd_5741144] using wordTrace_append hprefix tailTrace_5741144
  have hstable : (prefixWord ++ tailWord_5741144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741144).length < 2 ^ (prefixWord ++ tailWord_5741144).sum := by decide
  have hdescent : baseEnd_5741144 < baseStart_5741144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741191 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_5741191 : Nat := 118140960795 + 5741191 * 2 ^ 59
def prefixEnd_5741191 : Nat := 4983230072969 + 3 ^ 40 * 5741191 * 2
def baseEnd_5741191 : Nat := 2947990512267152297509249

theorem tailTrace_5741191 : CollatzResearch.WordTrace tailWord_5741191 prefixEnd_5741191 2947990512267152297509249 := by
  unfold tailWord_5741191
  simp only [CollatzResearch.WordTrace]
  refine ⟨209398438543652999204935427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139598959029101999469956951 209398438543652999204935427)
  ·
    refine ⟨314097657815479498807403141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209398438543652999204935427 314097657815479498807403141)
    ·
      refine ⟨58893310840402406026388089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314097657815479498807403141 58893310840402406026388089)
      ·
        refine ⟨44169983130301804519791067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58893310840402406026388089 44169983130301804519791067)
        ·
          refine ⟨66254974695452706779686601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44169983130301804519791067 66254974695452706779686601)
          ·
            refine ⟨49691231021589530084764951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66254974695452706779686601 49691231021589530084764951)
            ·
              refine ⟨74536846532384295127147427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49691231021589530084764951 74536846532384295127147427)
              ·
                refine ⟨111805269798576442690721141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74536846532384295127147427 111805269798576442690721141)
                ·
                  refine ⟨10481744043616541502255107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111805269798576442690721141 10481744043616541502255107)
                  ·
                    refine ⟨15722616065424812253382661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10481744043616541502255107 15722616065424812253382661)
                    ·
                      refine ⟨2947990512267152297509249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15722616065424812253382661 2947990512267152297509249)
                      ·
                        rfl

theorem cell23_5741191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_5741191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741191 prefixEnd_5741191 := by exact prefixLift 5741191
  have htrace : WordTrace (prefixWord ++ tailWord_5741191) baseStart_5741191 baseEnd_5741191 := by
    simpa [prefixWord, tailWord_5741191, baseEnd_5741191] using wordTrace_append hprefix tailTrace_5741191
  have hstable : (prefixWord ++ tailWord_5741191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741191).length < 2 ^ (prefixWord ++ tailWord_5741191).sum := by decide
  have hdescent : baseEnd_5741191 < baseStart_5741191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741208 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_5741208 : Nat := 118140960795 + 5741208 * 2 ^ 59
def prefixEnd_5741208 : Nat := 4983230072969 + 3 ^ 40 * 5741208 * 2
def baseEnd_5741208 : Nat := 2947999241438278730996671

theorem tailTrace_5741208 : CollatzResearch.WordTrace tailWord_5741208 prefixEnd_5741208 2947999241438278730996671 := by
  unfold tailWord_5741208
  simp only [CollatzResearch.WordTrace]
  refine ⟨104699529292295705554152139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139599372389727607405536185 104699529292295705554152139)
  ·
    refine ⟨157049293938443558331228209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104699529292295705554152139 157049293938443558331228209)
    ·
      refine ⟨117786970453832668748421157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157049293938443558331228209 117786970453832668748421157)
      ·
        refine ⟨22085056960093625390328967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117786970453832668748421157 22085056960093625390328967)
        ·
          refine ⟨33127585440140438085493451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22085056960093625390328967 33127585440140438085493451)
          ·
            refine ⟨49691378160210657128240177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33127585440140438085493451 49691378160210657128240177)
            ·
              refine ⟨37268533620157992846180133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49691378160210657128240177 37268533620157992846180133)
              ·
                refine ⟨6987850053779623658658775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37268533620157992846180133 6987850053779623658658775)
                ·
                  refine ⟨10481775080669435487988163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6987850053779623658658775 10481775080669435487988163)
                  ·
                    refine ⟨15722662621004153231982245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10481775080669435487988163 15722662621004153231982245)
                    ·
                      refine ⟨2947999241438278730996671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15722662621004153231982245 2947999241438278730996671)
                      ·
                        rfl

theorem cell23_5741208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_5741208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741208 prefixEnd_5741208 := by exact prefixLift 5741208
  have htrace : WordTrace (prefixWord ++ tailWord_5741208) baseStart_5741208 baseEnd_5741208 := by
    simpa [prefixWord, tailWord_5741208, baseEnd_5741208] using wordTrace_append hprefix tailTrace_5741208
  have hstable : (prefixWord ++ tailWord_5741208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741208).length < 2 ^ (prefixWord ++ tailWord_5741208).sum := by decide
  have hdescent : baseEnd_5741208 < baseStart_5741208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741212 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5741212 : Nat := 118140960795 + 5741212 * 2 ^ 59
def prefixEnd_5741212 : Nat := 4983230072969 + 3 ^ 40 * 5741212 * 2
def baseEnd_5741212 : Nat := 2948001295360896715346653

theorem tailTrace_5741212 : CollatzResearch.WordTrace tailWord_5741212 prefixEnd_5741212 2948001295360896715346653 := by
  unfold tailWord_5741212
  simp only [CollatzResearch.WordTrace]
  refine ⟨104699602238288459895724945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139599469651051279860966593 104699602238288459895724945)
  ·
    refine ⟨78524701678716344921793709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104699602238288459895724945 78524701678716344921793709)
    ·
      refine ⟨29446763129518629345672641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78524701678716344921793709 29446763129518629345672641)
      ·
        refine ⟨22085072347138972009254481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29446763129518629345672641 22085072347138972009254481)
        ·
          refine ⟨16563804260354229006940861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22085072347138972009254481 16563804260354229006940861)
          ·
            refine ⟨6211426597632835877602823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16563804260354229006940861 6211426597632835877602823)
            ·
              refine ⟨9317139896449253816404235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211426597632835877602823 9317139896449253816404235)
              ·
                refine ⟨13975709844673880724606353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9317139896449253816404235 13975709844673880724606353)
                ·
                  refine ⟨10481782383505410543454765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13975709844673880724606353 10481782383505410543454765)
                  ·
                    refine ⟨3930668393814528953795537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10481782383505410543454765 3930668393814528953795537)
                    ·
                      refine ⟨2948001295360896715346653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930668393814528953795537 2948001295360896715346653)
                      ·
                        rfl

theorem cell23_5741212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5741212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741212 prefixEnd_5741212 := by exact prefixLift 5741212
  have htrace : WordTrace (prefixWord ++ tailWord_5741212) baseStart_5741212 baseEnd_5741212 := by
    simpa [prefixWord, tailWord_5741212, baseEnd_5741212] using wordTrace_append hprefix tailTrace_5741212
  have hstable : (prefixWord ++ tailWord_5741212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741212).length < 2 ^ (prefixWord ++ tailWord_5741212).sum := by decide
  have hdescent : baseEnd_5741212 < baseStart_5741212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741235 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 2, 4]
def baseStart_5741235 : Nat := 118140960795 + 5741235 * 2 ^ 59
def prefixEnd_5741235 : Nat := 4983230072969 + 3 ^ 40 * 5741235 * 2
def baseEnd_5741235 : Nat := 982671035138650041786349

theorem tailTrace_5741235 : CollatzResearch.WordTrace tailWord_5741235 prefixEnd_5741235 982671035138650041786349 := by
  unfold tailWord_5741235
  simp only [CollatzResearch.WordTrace]
  refine ⟨209400043355493594719537159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139600028903662396479691439 209400043355493594719537159)
  ·
    refine ⟨314100065033240392079305739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209400043355493594719537159 314100065033240392079305739)
    ·
      refine ⟨471150097549860588118958609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314100065033240392079305739 471150097549860588118958609)
      ·
        refine ⟨353362573162395441089218957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471150097549860588118958609 353362573162395441089218957)
        ·
          refine ⟨132510964935898290408457109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353362573162395441089218957 132510964935898290408457109)
          ·
            refine ⟨6211451481370232362896427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132510964935898290408457109 6211451481370232362896427)
            ·
              refine ⟨9317177222055348544344641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211451481370232362896427 9317177222055348544344641)
              ·
                refine ⟨6987882916541511408258481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9317177222055348544344641 6987882916541511408258481)
                ·
                  refine ⟨5240912187406133556193861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6987882916541511408258481 5240912187406133556193861)
                  ·
                    refine ⟨982671035138650041786349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5240912187406133556193861 982671035138650041786349)
                    ·
                      rfl

theorem cell23_5741235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 4].length) (baseStart_5741235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741235 prefixEnd_5741235 := by exact prefixLift 5741235
  have htrace : WordTrace (prefixWord ++ tailWord_5741235) baseStart_5741235 baseEnd_5741235 := by
    simpa [prefixWord, tailWord_5741235, baseEnd_5741235] using wordTrace_append hprefix tailTrace_5741235
  have hstable : (prefixWord ++ tailWord_5741235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741235).length < 2 ^ (prefixWord ++ tailWord_5741235).sum := by decide
  have hdescent : baseEnd_5741235 < baseStart_5741235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741242 : List Nat := [3, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2]
def baseStart_5741242 : Nat := 118140960795 + 5741242 * 2 ^ 59
def prefixEnd_5741242 : Nat := 4983230072969 + 3 ^ 40 * 5741242 * 2
def baseEnd_5741242 : Nat := 2948016699780531597971515

theorem tailTrace_5741242 : CollatzResearch.WordTrace tailWord_5741242 prefixEnd_5741242 2948016699780531597971515 := by
  unfold tailWord_5741242
  simp only [CollatzResearch.WordTrace]
  refine ⟨52350074666617058728760495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139600199110978823276694653 52350074666617058728760495)
  ·
    refine ⟨78525111999925588093140743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52350074666617058728760495 78525111999925588093140743)
    ·
      refine ⟨117787667999888382139711115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78525111999925588093140743 117787667999888382139711115)
      ·
        refine ⟨176681501999832573209566673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117787667999888382139711115 176681501999832573209566673)
        ·
          refine ⟨132511126499874429907175005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176681501999832573209566673 132511126499874429907175005)
          ·
            refine ⟨49691672437452911215190627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132511126499874429907175005 49691672437452911215190627)
            ·
              refine ⟨74537508656179366822785941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49691672437452911215190627 74537508656179366822785941)
              ·
                refine ⟨3493945718258407819818091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74537508656179366822785941 3493945718258407819818091)
                ·
                  refine ⟨5240918577387611729727137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493945718258407819818091 5240918577387611729727137)
                  ·
                    refine ⟨3930688933040708797295353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240918577387611729727137 3930688933040708797295353)
                    ·
                      refine ⟨2948016699780531597971515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930688933040708797295353 2948016699780531597971515)
                      ·
                        rfl

theorem cell23_5741242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_5741242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741242 prefixEnd_5741242 := by exact prefixLift 5741242
  have htrace : WordTrace (prefixWord ++ tailWord_5741242) baseStart_5741242 baseEnd_5741242 := by
    simpa [prefixWord, tailWord_5741242, baseEnd_5741242] using wordTrace_append hprefix tailTrace_5741242
  have hstable : (prefixWord ++ tailWord_5741242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741242).length < 2 ^ (prefixWord ++ tailWord_5741242).sum := by decide
  have hdescent : baseEnd_5741242 < baseStart_5741242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741252 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5741252 : Nat := 118140960795 + 5741252 * 2 ^ 59
def prefixEnd_5741252 : Nat := 4983230072969 + 3 ^ 40 * 5741252 * 2
def baseEnd_5741252 : Nat := 982673944862358852948823

theorem tailTrace_5741252 : CollatzResearch.WordTrace tailWord_5741252 prefixEnd_5741252 982673944862358852948823 := by
  unfold tailWord_5741252
  simp only [CollatzResearch.WordTrace]
  refine ⟨104700331698216003311453005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139600442264288004415270673 104700331698216003311453005)
  ·
    refine ⟨39262624386831001241794877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104700331698216003311453005 39262624386831001241794877)
    ·
      refine ⟨14723484145061625465673079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39262624386831001241794877 14723484145061625465673079)
      ·
        refine ⟨22085226217592438198509619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14723484145061625465673079 22085226217592438198509619)
        ·
          refine ⟨33127839326388657297764429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22085226217592438198509619 33127839326388657297764429)
          ·
            refine ⟨12422939747395746486661661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33127839326388657297764429 12422939747395746486661661)
            ·
              refine ⟨4658602405273404932498123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12422939747395746486661661 4658602405273404932498123)
              ·
                refine ⟨6987903607910107398747185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658602405273404932498123 6987903607910107398747185)
                ·
                  refine ⟨5240927705932580549060389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6987903607910107398747185 5240927705932580549060389)
                  ·
                    refine ⟨982673944862358852948823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5240927705932580549060389 982673944862358852948823)
                    ·
                      rfl

theorem cell23_5741252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5741252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741252 prefixEnd_5741252 := by exact prefixLift 5741252
  have htrace : WordTrace (prefixWord ++ tailWord_5741252) baseStart_5741252 baseEnd_5741252 := by
    simpa [prefixWord, tailWord_5741252, baseEnd_5741252] using wordTrace_append hprefix tailTrace_5741252
  have hstable : (prefixWord ++ tailWord_5741252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741252).length < 2 ^ (prefixWord ++ tailWord_5741252).sum := by decide
  have hdescent : baseEnd_5741252 < baseStart_5741252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741271 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_5741271 : Nat := 118140960795 + 5741271 * 2 ^ 59
def prefixEnd_5741271 : Nat := 4983230072969 + 3 ^ 40 * 5741271 * 2
def baseEnd_5741271 : Nat := 2948031590719511984508881

theorem tailTrace_5741271 : CollatzResearch.WordTrace tailWord_5741271 prefixEnd_5741271 2948031590719511984508881 := by
  unfold tailWord_5741271
  simp only [CollatzResearch.WordTrace]
  refine ⟨209401356383363172867847667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139600904255575448578565111 209401356383363172867847667)
  ·
    refine ⟨314102034575044759301771501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209401356383363172867847667 314102034575044759301771501)
    ·
      refine ⟨117788262965641784738164313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314102034575044759301771501 117788262965641784738164313)
      ·
        refine ⟨88341197224231338553623235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117788262965641784738164313 88341197224231338553623235)
        ·
          refine ⟨132511795836347007830434853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88341197224231338553623235 132511795836347007830434853)
          ·
            refine ⟨24845961719315063968206535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132511795836347007830434853 24845961719315063968206535)
            ·
              refine ⟨37268942578972595952309803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24845961719315063968206535 37268942578972595952309803)
              ·
                refine ⟨55903413868458893928464705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37268942578972595952309803 55903413868458893928464705)
                ·
                  refine ⟨41927560401344170446348529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55903413868458893928464705 41927560401344170446348529)
                  ·
                    refine ⟨31445670301008127834761397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41927560401344170446348529 31445670301008127834761397)
                    ·
                      refine ⟨2948031590719511984508881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31445670301008127834761397 2948031590719511984508881)
                      ·
                        rfl

theorem cell23_5741271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_5741271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741271 prefixEnd_5741271 := by exact prefixLift 5741271
  have htrace : WordTrace (prefixWord ++ tailWord_5741271) baseStart_5741271 baseEnd_5741271 := by
    simpa [prefixWord, tailWord_5741271, baseEnd_5741271] using wordTrace_append hprefix tailTrace_5741271
  have hstable : (prefixWord ++ tailWord_5741271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741271).length < 2 ^ (prefixWord ++ tailWord_5741271).sum := by decide
  have hdescent : baseEnd_5741271 < baseStart_5741271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741276 : List Nat := [2, 2, 5, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5741276 : Nat := 118140960795 + 5741276 * 2 ^ 59
def prefixEnd_5741276 : Nat := 4983230072969 + 3 ^ 40 * 5741276 * 2
def baseEnd_5741276 : Nat := 2948034158122784464946359

theorem tailTrace_5741276 : CollatzResearch.WordTrace tailWord_5741276 prefixEnd_5741276 2948034158122784464946359 := by
  unfold tailWord_5741276
  simp only [CollatzResearch.WordTrace]
  refine ⟨104700769374172529360889841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139601025832230039147853121 104700769374172529360889841)
  ·
    refine ⟨78525577030629397020667381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104700769374172529360889841 78525577030629397020667381)
    ·
      refine ⟨7361772846621505970687567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78525577030629397020667381 7361772846621505970687567)
      ·
        refine ⟨11042659269932258956031351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7361772846621505970687567 11042659269932258956031351)
        ·
          refine ⟨16563988904898388434047027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11042659269932258956031351 16563988904898388434047027)
          ·
            refine ⟨24845983357347582651070541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16563988904898388434047027 24845983357347582651070541)
            ·
              refine ⟨9317243759005343494151453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24845983357347582651070541 9317243759005343494151453)
              ·
                refine ⟨3493966409627003810306795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9317243759005343494151453 3493966409627003810306795)
                ·
                  refine ⟨5240949614440505715460193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3493966409627003810306795 5240949614440505715460193)
                  ·
                    refine ⟨3930712210830379286595145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5240949614440505715460193 3930712210830379286595145)
                    ·
                      refine ⟨2948034158122784464946359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930712210830379286595145 2948034158122784464946359)
                      ·
                        rfl

theorem cell23_5741276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5741276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741276 prefixEnd_5741276 := by exact prefixLift 5741276
  have htrace : WordTrace (prefixWord ++ tailWord_5741276) baseStart_5741276 baseEnd_5741276 := by
    simpa [prefixWord, tailWord_5741276, baseEnd_5741276] using wordTrace_append hprefix tailTrace_5741276
  have hstable : (prefixWord ++ tailWord_5741276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741276).length < 2 ^ (prefixWord ++ tailWord_5741276).sum := by decide
  have hdescent : baseEnd_5741276 < baseStart_5741276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741311 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_5741311 : Nat := 118140960795 + 5741311 * 2 ^ 59
def prefixEnd_5741311 : Nat := 4983230072969 + 3 ^ 40 * 5741311 * 2
def baseEnd_5741311 : Nat := 2948052129945691828008697

theorem tailTrace_5741311 : CollatzResearch.WordTrace tailWord_5741311 prefixEnd_5741311 2948052129945691828008697 := by
  unfold tailWord_5741311
  simp only [CollatzResearch.WordTrace]
  refine ⟨209402815303218259699303787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139601876868812173132869191 209402815303218259699303787)
  ·
    refine ⟨314104222954827389548955681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209402815303218259699303787 314104222954827389548955681)
    ·
      refine ⟨235578167216120542161716761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314104222954827389548955681 235578167216120542161716761)
      ·
        refine ⟨176683625412090406621287571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235578167216120542161716761 176683625412090406621287571)
        ·
          refine ⟨265025438118135609931931357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176683625412090406621287571 265025438118135609931931357)
          ·
            refine ⟨99384539294300853724474259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 265025438118135609931931357 99384539294300853724474259)
            ·
              refine ⟨149076808941451280586711389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99384539294300853724474259 149076808941451280586711389)
              ·
                refine ⟨55903803353044230220016771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149076808941451280586711389 55903803353044230220016771)
                ·
                  refine ⟨83855705029566345330025157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55903803353044230220016771 83855705029566345330025157)
                  ·
                    refine ⟨15722944693043689749379717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83855705029566345330025157 15722944693043689749379717)
                    ·
                      refine ⟨2948052129945691828008697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15722944693043689749379717 2948052129945691828008697)
                      ·
                        rfl

theorem cell23_5741311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_5741311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741311 prefixEnd_5741311 := by exact prefixLift 5741311
  have htrace : WordTrace (prefixWord ++ tailWord_5741311) baseStart_5741311 baseEnd_5741311 := by
    simpa [prefixWord, tailWord_5741311, baseEnd_5741311] using wordTrace_append hprefix tailTrace_5741311
  have hstable : (prefixWord ++ tailWord_5741311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741311).length < 2 ^ (prefixWord ++ tailWord_5741311).sum := by decide
  have hdescent : baseEnd_5741311 < baseStart_5741311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741319 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5741319 : Nat := 118140960795 + 5741319 * 2 ^ 59
def prefixEnd_5741319 : Nat := 4983230072969 + 3 ^ 40 * 5741319 * 2
def baseEnd_5741319 : Nat := 2948056237790927796708661

theorem tailTrace_5741319 : CollatzResearch.WordTrace tailWord_5741319 prefixEnd_5741319 2948056237790927796708661 := by
  unfold tailWord_5741319
  simp only [CollatzResearch.WordTrace]
  refine ⟨209403107087189277065595011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139602071391459518043730007 209403107087189277065595011)
  ·
    refine ⟨314104660630783915598392517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209403107087189277065595011 314104660630783915598392517)
    ·
      refine ⟨58894623868271984174698597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314104660630783915598392517 58894623868271984174698597)
      ·
        refine ⟨11042741975300997032755987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58894623868271984174698597 11042741975300997032755987)
        ·
          refine ⟨16564112962951495549133981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11042741975300997032755987 16564112962951495549133981)
          ·
            refine ⟨6211542361106810830925243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16564112962951495549133981 6211542361106810830925243)
            ·
              refine ⟨9317313541660216246387865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211542361106810830925243 9317313541660216246387865)
              ·
                refine ⟨6987985156245162184790899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9317313541660216246387865 6987985156245162184790899)
                ·
                  refine ⟨10481977734367743277186349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6987985156245162184790899 10481977734367743277186349)
                  ·
                    refine ⟨3930741650387903728944881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10481977734367743277186349 3930741650387903728944881)
                    ·
                      refine ⟨2948056237790927796708661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930741650387903728944881 2948056237790927796708661)
                      ·
                        rfl

theorem cell23_5741319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5741319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741319 prefixEnd_5741319 := by exact prefixLift 5741319
  have htrace : WordTrace (prefixWord ++ tailWord_5741319) baseStart_5741319 baseEnd_5741319 := by
    simpa [prefixWord, tailWord_5741319, baseEnd_5741319] using wordTrace_append hprefix tailTrace_5741319
  have hstable : (prefixWord ++ tailWord_5741319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741319).length < 2 ^ (prefixWord ++ tailWord_5741319).sum := by decide
  have hdescent : baseEnd_5741319 < baseStart_5741319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741321 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 7]
def baseStart_5741321 : Nat := 118140960795 + 5741321 * 2 ^ 59
def prefixEnd_5741321 : Nat := 4983230072969 + 3 ^ 40 * 5741321 * 2
def baseEnd_5741321 : Nat := 327561918305804087653739

theorem tailTrace_5741321 : CollatzResearch.WordTrace tailWord_5741321 prefixEnd_5741321 327561918305804087653739 := by
  unfold tailWord_5741321
  simp only [CollatzResearch.WordTrace]
  refine ⟨209403180033182031407167817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139602120022121354271445211 209403180033182031407167817)
  ·
    refine ⟨157052385024886523555375863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209403180033182031407167817 157052385024886523555375863)
    ·
      refine ⟨235578577537329785333063795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157052385024886523555375863 235578577537329785333063795)
      ·
        refine ⟨353367866305994677999595693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235578577537329785333063795 353367866305994677999595693)
        ·
          refine ⟨132512949864748004249848385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353367866305994677999595693 132512949864748004249848385)
          ·
            refine ⟨99384712398561003187386289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132512949864748004249848385 99384712398561003187386289)
            ·
              refine ⟨74538534298920752390539717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99384712398561003187386289 74538534298920752390539717)
              ·
                refine ⟨13975975181047641073226197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74538534298920752390539717 13975975181047641073226197)
                ·
                  refine ⟨327561918305804087653739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13975975181047641073226197 327561918305804087653739)
                  ·
                    rfl

theorem cell23_5741321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 7].length) (baseStart_5741321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741321 prefixEnd_5741321 := by exact prefixLift 5741321
  have htrace : WordTrace (prefixWord ++ tailWord_5741321) baseStart_5741321 baseEnd_5741321 := by
    simpa [prefixWord, tailWord_5741321, baseEnd_5741321] using wordTrace_append hprefix tailTrace_5741321
  have hstable : (prefixWord ++ tailWord_5741321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741321).length < 2 ^ (prefixWord ++ tailWord_5741321).sum := by decide
  have hdescent : baseEnd_5741321 < baseStart_5741321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741365 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_5741365 : Nat := 118140960795 + 5741365 * 2 ^ 59
def prefixEnd_5741365 : Nat := 4983230072969 + 3 ^ 40 * 5741365 * 2
def baseEnd_5741365 : Nat := 2948079857901034616733449

theorem tailTrace_5741365 : CollatzResearch.WordTrace tailWord_5741365 prefixEnd_5741365 2948079857901034616733449 := by
  unfold tailWord_5741365
  simp only [CollatzResearch.WordTrace]
  refine ⟨209404784845022626921769549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139603189896681751281179699 209404784845022626921769549)
  ·
    refine ⟨78526794316883485095663581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209404784845022626921769549 78526794316883485095663581)
    ·
      refine ⟨29447547868831306910873843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78526794316883485095663581 29447547868831306910873843)
      ·
        refine ⟨44171321803246960366310765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29447547868831306910873843 44171321803246960366310765)
        ·
          refine ⟨16564245676217610137366537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44171321803246960366310765 16564245676217610137366537)
          ·
            refine ⟨12423184257163207603024903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16564245676217610137366537 12423184257163207603024903)
            ·
              refine ⟨18634776385744811404537355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12423184257163207603024903 18634776385744811404537355)
              ·
                refine ⟨27952164578617217106806033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18634776385744811404537355 27952164578617217106806033)
                ·
                  refine ⟨20964123433962912830104525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27952164578617217106806033 20964123433962912830104525)
                  ·
                    refine ⟨7861546287736092311289197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20964123433962912830104525 7861546287736092311289197)
                    ·
                      refine ⟨2948079857901034616733449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7861546287736092311289197 2948079857901034616733449)
                      ·
                        rfl

theorem cell23_5741365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_5741365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741365 prefixEnd_5741365 := by exact prefixLift 5741365
  have htrace : WordTrace (prefixWord ++ tailWord_5741365) baseStart_5741365 baseEnd_5741365 := by
    simpa [prefixWord, tailWord_5741365, baseEnd_5741365] using wordTrace_append hprefix tailTrace_5741365
  have hstable : (prefixWord ++ tailWord_5741365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741365).length < 2 ^ (prefixWord ++ tailWord_5741365).sum := by decide
  have hdescent : baseEnd_5741365 < baseStart_5741365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741381 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_5741381 : Nat := 118140960795 + 5741381 * 2 ^ 59
def prefixEnd_5741381 : Nat := 4983230072969 + 3 ^ 40 * 5741381 * 2
def baseEnd_5741381 : Nat := 982696024530502184711125

theorem tailTrace_5741381 : CollatzResearch.WordTrace tailWord_5741381 prefixEnd_5741381 982696024530502184711125 := by
  unfold tailWord_5741381
  simp only [CollatzResearch.WordTrace]
  refine ⟨209405368412964661654351997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139603578941976441102901331 209405368412964661654351997)
  ·
    refine ⟨78527013154861748120381999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209405368412964661654351997 78527013154861748120381999)
    ·
      refine ⟨117790519732292622180572999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78527013154861748120381999 117790519732292622180572999)
      ·
        refine ⟨176685779598438933270859499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117790519732292622180572999 176685779598438933270859499)
        ·
          refine ⟨265028669397658399906289249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176685779598438933270859499 265028669397658399906289249)
          ·
            refine ⟨198771502048243799929716937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265028669397658399906289249 198771502048243799929716937)
            ·
              refine ⟨149078626536182849947287703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198771502048243799929716937 149078626536182849947287703)
              ·
                refine ⟨223617939804274274920931555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149078626536182849947287703 223617939804274274920931555)
                ·
                  refine ⟨335426909706411412381397333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223617939804274274920931555 335426909706411412381397333)
                  ·
                    refine ⟨982696024530502184711125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 335426909706411412381397333 982696024530502184711125)
                    ·
                      rfl

theorem cell23_5741381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_5741381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741381 prefixEnd_5741381 := by exact prefixLift 5741381
  have htrace : WordTrace (prefixWord ++ tailWord_5741381) baseStart_5741381 baseEnd_5741381 := by
    simpa [prefixWord, tailWord_5741381, baseEnd_5741381] using wordTrace_append hprefix tailTrace_5741381
  have hstable : (prefixWord ++ tailWord_5741381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741381).length < 2 ^ (prefixWord ++ tailWord_5741381).sum := by decide
  have hdescent : baseEnd_5741381 < baseStart_5741381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741385 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 2, 5]
def baseStart_5741385 : Nat := 118140960795 + 5741385 * 2 ^ 59
def prefixEnd_5741385 : Nat := 4983230072969 + 3 ^ 40 * 5741385 * 2
def baseEnd_5741385 : Nat := 982696709171374846161119

theorem tailTrace_5741385 : CollatzResearch.WordTrace tailWord_5741385 prefixEnd_5741385 982696709171374846161119 := by
  unfold tailWord_5741385
  simp only [CollatzResearch.WordTrace]
  refine ⟨209405514304950170337497609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139603676203300113558331739 209405514304950170337497609)
  ·
    refine ⟨157054135728712627753123207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209405514304950170337497609 157054135728712627753123207)
    ·
      refine ⟨235581203593068941629684811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157054135728712627753123207 235581203593068941629684811)
      ·
        refine ⟨353371805389603412444527217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235581203593068941629684811 353371805389603412444527217)
        ·
          refine ⟨265028854042202559333395413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353371805389603412444527217 265028854042202559333395413)
          ·
            refine ⟨6211613766614122484376455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 265028854042202559333395413 6211613766614122484376455)
            ·
              refine ⟨9317420649921183726564683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211613766614122484376455 9317420649921183726564683)
              ·
                refine ⟨13976130974881775589847025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9317420649921183726564683 13976130974881775589847025)
                ·
                  refine ⟨10482098231161331692385269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13976130974881775589847025 10482098231161331692385269)
                  ·
                    refine ⟨982696709171374846161119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10482098231161331692385269 982696709171374846161119)
                    ·
                      rfl

theorem cell23_5741385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_5741385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741385 prefixEnd_5741385 := by exact prefixLift 5741385
  have htrace : WordTrace (prefixWord ++ tailWord_5741385) baseStart_5741385 baseEnd_5741385 := by
    simpa [prefixWord, tailWord_5741385, baseEnd_5741385] using wordTrace_append hprefix tailTrace_5741385
  have hstable : (prefixWord ++ tailWord_5741385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741385).length < 2 ^ (prefixWord ++ tailWord_5741385).sum := by decide
  have hdescent : baseEnd_5741385 < baseStart_5741385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741389 : List Nat := [1, 6, 1, 2, 2, 1, 2, 3, 5]
def baseStart_5741389 : Nat := 118140960795 + 5741389 * 2 ^ 59
def prefixEnd_5741389 : Nat := 4983230072969 + 3 ^ 40 * 5741389 * 2
def baseEnd_5741389 : Nat := 327565797937415835870371

theorem tailTrace_5741389 : CollatzResearch.WordTrace tailWord_5741389 prefixEnd_5741389 327565797937415835870371 := by
  unfold tailWord_5741389
  simp only [CollatzResearch.WordTrace]
  refine ⟨209405660196935679020643221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139603773464623786013762147 209405660196935679020643221)
  ·
    refine ⟨9815890321731359954092651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 209405660196935679020643221 9815890321731359954092651)
    ·
      refine ⟨14723835482597039931138977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9815890321731359954092651 14723835482597039931138977)
      ·
        refine ⟨11042876611947779948354233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14723835482597039931138977 11042876611947779948354233)
        ·
          refine ⟨8282157458960834961265675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11042876611947779948354233 8282157458960834961265675)
          ·
            refine ⟨12423236188441252441898513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8282157458960834961265675 12423236188441252441898513)
            ·
              refine ⟨9317427141330939331423885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12423236188441252441898513 9317427141330939331423885)
              ·
                refine ⟨3494035177999102249283957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9317427141330939331423885 3494035177999102249283957)
                ·
                  refine ⟨327565797937415835870371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3494035177999102249283957 327565797937415835870371)
                  ·
                    rfl

theorem cell23_5741389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_5741389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741389 prefixEnd_5741389 := by exact prefixLift 5741389
  have htrace : WordTrace (prefixWord ++ tailWord_5741389) baseStart_5741389 baseEnd_5741389 := by
    simpa [prefixWord, tailWord_5741389, baseEnd_5741389] using wordTrace_append hprefix tailTrace_5741389
  have hstable : (prefixWord ++ tailWord_5741389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741389).length < 2 ^ (prefixWord ++ tailWord_5741389).sum := by decide
  have hdescent : baseEnd_5741389 < baseStart_5741389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741415 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 3, 4]
def baseStart_5741415 : Nat := 118140960795 + 5741415 * 2 ^ 59
def prefixEnd_5741415 : Nat := 4983230072969 + 3 ^ 40 * 5741415 * 2
def baseEnd_5741415 : Nat := 982701843977919807036073

theorem tailTrace_5741415 : CollatzResearch.WordTrace tailWord_5741415 prefixEnd_5741415 982701843977919807036073 := by
  unfold tailWord_5741415
  simp only [CollatzResearch.WordTrace]
  refine ⟨209406608494841485461089699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139604405663227656974059799 209406608494841485461089699)
  ·
    refine ⟨314109912742262228191634549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209406608494841485461089699 314109912742262228191634549)
    ·
      refine ⟨29447804319587083892965739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 314109912742262228191634549 29447804319587083892965739)
      ·
        refine ⟨44171706479380625839448609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29447804319587083892965739 44171706479380625839448609)
        ·
          refine ⟨33128779859535469379586457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44171706479380625839448609 33128779859535469379586457)
          ·
            refine ⟨24846584894651602034689843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33128779859535469379586457 24846584894651602034689843)
            ·
              refine ⟨37269877341977403052034765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24846584894651602034689843 37269877341977403052034765)
              ·
                refine ⟨13976204003241526144513037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37269877341977403052034765 13976204003241526144513037)
                ·
                  refine ⟨5241076501215572304192389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13976204003241526144513037 5241076501215572304192389)
                  ·
                    refine ⟨982701843977919807036073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241076501215572304192389 982701843977919807036073)
                    ·
                      rfl

theorem cell23_5741415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_5741415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741415 prefixEnd_5741415 := by exact prefixLift 5741415
  have htrace : WordTrace (prefixWord ++ tailWord_5741415) baseStart_5741415 baseEnd_5741415 := by
    simpa [prefixWord, tailWord_5741415, baseEnd_5741415] using wordTrace_append hprefix tailTrace_5741415
  have hstable : (prefixWord ++ tailWord_5741415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741415).length < 2 ^ (prefixWord ++ tailWord_5741415).sum := by decide
  have hdescent : baseEnd_5741415 < baseStart_5741415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741449 : List Nat := [1, 2, 1, 1, 5, 4, 1, 3, 1, 4]
def baseStart_5741449 : Nat := 118140960795 + 5741449 * 2 ^ 59
def prefixEnd_5741449 : Nat := 4983230072969 + 3 ^ 40 * 5741449 * 2
def baseEnd_5741449 : Nat := 982707663425337429361021

theorem tailTrace_5741449 : CollatzResearch.WordTrace tailWord_5741449 prefixEnd_5741449 982707663425337429361021 := by
  unfold tailWord_5741449
  simp only [CollatzResearch.WordTrace]
  refine ⟨209407848576718309267827401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139605232384478872845218267 209407848576718309267827401)
  ·
    refine ⟨157055886432538731950870551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209407848576718309267827401 157055886432538731950870551)
    ·
      refine ⟨235583829648808097926305827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157055886432538731950870551 235583829648808097926305827)
      ·
        refine ⟨353375744473212146889458741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235583829648808097926305827 353375744473212146889458741)
        ·
          refine ⟨33128976044363638770886757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 353375744473212146889458741 33128976044363638770886757)
          ·
            refine ⟨6211683008318182269541267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33128976044363638770886757 6211683008318182269541267)
            ·
              refine ⟨9317524512477273404311901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211683008318182269541267 9317524512477273404311901)
              ·
                refine ⟨3494071692178977526616963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9317524512477273404311901 3494071692178977526616963)
                ·
                  refine ⟨5241107538268466289925445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494071692178977526616963 5241107538268466289925445)
                  ·
                    refine ⟨982707663425337429361021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241107538268466289925445 982707663425337429361021)
                    ·
                      rfl

theorem cell23_5741449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 1, 4].length) (baseStart_5741449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741449 prefixEnd_5741449 := by exact prefixLift 5741449
  have htrace : WordTrace (prefixWord ++ tailWord_5741449) baseStart_5741449 baseEnd_5741449 := by
    simpa [prefixWord, tailWord_5741449, baseEnd_5741449] using wordTrace_append hprefix tailTrace_5741449
  have hstable : (prefixWord ++ tailWord_5741449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741449).length < 2 ^ (prefixWord ++ tailWord_5741449).sum := by decide
  have hdescent : baseEnd_5741449 < baseStart_5741449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741466 : List Nat := [3, 1, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_5741466 : Nat := 118140960795 + 5741466 * 2 ^ 59
def prefixEnd_5741466 : Nat := 4983230072969 + 3 ^ 40 * 5741466 * 2
def baseEnd_5741466 : Nat := 982710573149046240523495

theorem tailTrace_5741466 : CollatzResearch.WordTrace tailWord_5741466 prefixEnd_5741466 982710573149046240523495 := by
  unfold tailWord_5741466
  simp only [CollatzResearch.WordTrace]
  refine ⟨52352117154414180292799063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139605645745104480780797501 52352117154414180292799063)
  ·
    refine ⟨78528175731621270439198595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52352117154414180292799063 78528175731621270439198595)
    ·
      refine ⟨117792263597431905658797893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78528175731621270439198595 117792263597431905658797893)
      ·
        refine ⟨22086049424518482311024605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117792263597431905658797893 22086049424518482311024605)
        ·
          refine ⟨8282268534194430866634227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22086049424518482311024605 8282268534194430866634227)
          ·
            refine ⟨12423402801291646299951341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8282268534194430866634227 12423402801291646299951341)
            ·
              refine ⟨4658776050484367362481753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12423402801291646299951341 4658776050484367362481753)
              ·
                refine ⟨3494082037863275521861315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4658776050484367362481753 3494082037863275521861315)
                ·
                  refine ⟨5241123056794913282791973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494082037863275521861315 5241123056794913282791973)
                  ·
                    refine ⟨982710573149046240523495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241123056794913282791973 982710573149046240523495)
                    ·
                      rfl

theorem cell23_5741466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_5741466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741466 prefixEnd_5741466 := by exact prefixLift 5741466
  have htrace : WordTrace (prefixWord ++ tailWord_5741466) baseStart_5741466 baseEnd_5741466 := by
    simpa [prefixWord, tailWord_5741466, baseEnd_5741466] using wordTrace_append hprefix tailTrace_5741466
  have hstable : (prefixWord ++ tailWord_5741466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741466).length < 2 ^ (prefixWord ++ tailWord_5741466).sum := by decide
  have hdescent : baseEnd_5741466 < baseStart_5741466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741472 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 3, 1, 3]
def baseStart_5741472 : Nat := 118140960795 + 5741472 * 2 ^ 59
def prefixEnd_5741472 : Nat := 4983230072969 + 3 ^ 40 * 5741472 * 2
def baseEnd_5741472 : Nat := 2948134800331065698095457

theorem tailTrace_5741472 : CollatzResearch.WordTrace tailWord_5741472 prefixEnd_5741472 2948134800331065698095457 := by
  unfold tailWord_5741472
  simp only [CollatzResearch.WordTrace]
  refine ⟨104704343727817492097957335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139605791637089989463943113 104704343727817492097957335)
  ·
    refine ⟨157056515591726238146936003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104704343727817492097957335 157056515591726238146936003)
    ·
      refine ⟨235584773387589357220404005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157056515591726238146936003 235584773387589357220404005)
      ·
        refine ⟨44172145010173004478825751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235584773387589357220404005 44172145010173004478825751)
        ·
          refine ⟨66258217515259506718238627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44172145010173004478825751 66258217515259506718238627)
          ·
            refine ⟨99387326272889260077357941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66258217515259506718238627 99387326272889260077357941)
            ·
              refine ⟨9317561838083368132252307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99387326272889260077357941 9317561838083368132252307)
              ·
                refine ⟨13976342757125052198378461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9317561838083368132252307 13976342757125052198378461)
                ·
                  refine ⟨5241128533921894574391923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13976342757125052198378461 5241128533921894574391923)
                  ·
                    refine ⟨7861692800882841861587885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241128533921894574391923 7861692800882841861587885)
                    ·
                      refine ⟨2948134800331065698095457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7861692800882841861587885 2948134800331065698095457)
                      ·
                        rfl

theorem cell23_5741472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_5741472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741472 prefixEnd_5741472 := by exact prefixLift 5741472
  have htrace : WordTrace (prefixWord ++ tailWord_5741472) baseStart_5741472 baseEnd_5741472 := by
    simpa [prefixWord, tailWord_5741472, baseEnd_5741472] using wordTrace_append hprefix tailTrace_5741472
  have hstable : (prefixWord ++ tailWord_5741472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741472).length < 2 ^ (prefixWord ++ tailWord_5741472).sum := by decide
  have hdescent : baseEnd_5741472 < baseStart_5741472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741479 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 6]
def baseStart_5741479 : Nat := 118140960795 + 5741479 * 2 ^ 59
def prefixEnd_5741479 : Nat := 4983230072969 + 3 ^ 40 * 5741479 * 2
def baseEnd_5741479 : Nat := 327570932743960796745325

theorem tailTrace_5741479 : CollatzResearch.WordTrace tailWord_5741479 prefixEnd_5741479 327570932743960796745325 := by
  unfold tailWord_5741479
  simp only [CollatzResearch.WordTrace]
  refine ⟨209408942766609624391419491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139605961844406416260946327 209408942766609624391419491)
  ·
    refine ⟨314113414149914436587129237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209408942766609624391419491 314113414149914436587129237)
    ·
      refine ⟨14724066288277239215021683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 314113414149914436587129237 14724066288277239215021683)
      ·
        refine ⟨22086099432415858822532525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14724066288277239215021683 22086099432415858822532525)
        ·
          refine ⟨8282287287155947058449697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22086099432415858822532525 8282287287155947058449697)
          ·
            refine ⟨6211715465366960293837273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8282287287155947058449697 6211715465366960293837273)
            ·
              refine ⟨4658786599025220220377955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6211715465366960293837273 4658786599025220220377955)
              ·
                refine ⟨6988179898537830330566933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658786599025220220377955 6988179898537830330566933)
                ·
                  refine ⟨327570932743960796745325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6988179898537830330566933 327570932743960796745325)
                  ·
                    rfl

theorem cell23_5741479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 6].length) (baseStart_5741479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741479 prefixEnd_5741479 := by exact prefixLift 5741479
  have htrace : WordTrace (prefixWord ++ tailWord_5741479) baseStart_5741479 baseEnd_5741479 := by
    simpa [prefixWord, tailWord_5741479, baseEnd_5741479] using wordTrace_append hprefix tailTrace_5741479
  have hstable : (prefixWord ++ tailWord_5741479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741479).length < 2 ^ (prefixWord ++ tailWord_5741479).sum := by decide
  have hdescent : baseEnd_5741479 < baseStart_5741479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741495 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 2, 6, 2]
def baseStart_5741495 : Nat := 118140960795 + 5741495 * 2 ^ 59
def prefixEnd_5741495 : Nat := 4983230072969 + 3 ^ 40 * 5741495 * 2
def baseEnd_5741495 : Nat := 2948146610386119108107851

theorem tailTrace_5741495 : CollatzResearch.WordTrace tailWord_5741495 prefixEnd_5741495 2948146610386119108107851 := by
  unfold tailWord_5741495
  simp only [CollatzResearch.WordTrace]
  refine ⟨209409526334551659124001939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139606350889701106082667959 209409526334551659124001939)
  ·
    refine ⟨314114289501827488686002909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209409526334551659124001939 314114289501827488686002909)
    ·
      refine ⟨117792858563185308257251091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314114289501827488686002909 117792858563185308257251091)
      ·
        refine ⟨176689287844777962385876637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117792858563185308257251091 176689287844777962385876637)
        ·
          refine ⟨66258482941791735894703739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176689287844777962385876637 66258482941791735894703739)
          ·
            refine ⟨99387724412687603842055609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66258482941791735894703739 99387724412687603842055609)
            ·
              refine ⟨74540793309515702881541707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99387724412687603842055609 74540793309515702881541707)
              ·
                refine ⟨111811189964273554322312561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74540793309515702881541707 111811189964273554322312561)
                ·
                  refine ⟨83858392473205165741734421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111811189964273554322312561 83858392473205165741734421)
                  ·
                    refine ⟨3930862147181492144143801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83858392473205165741734421 3930862147181492144143801)
                    ·
                      refine ⟨2948146610386119108107851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3930862147181492144143801 2948146610386119108107851)
                      ·
                        rfl

theorem cell23_5741495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_5741495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741495 prefixEnd_5741495 := by exact prefixLift 5741495
  have htrace : WordTrace (prefixWord ++ tailWord_5741495) baseStart_5741495 baseEnd_5741495 := by
    simpa [prefixWord, tailWord_5741495, baseEnd_5741495] using wordTrace_append hprefix tailTrace_5741495
  have hstable : (prefixWord ++ tailWord_5741495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741495).length < 2 ^ (prefixWord ++ tailWord_5741495).sum := by decide
  have hdescent : baseEnd_5741495 < baseStart_5741495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741515 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 5]
def baseStart_5741515 : Nat := 118140960795 + 5741515 * 2 ^ 59
def prefixEnd_5741515 : Nat := 4983230072969 + 3 ^ 40 * 5741515 * 2
def baseEnd_5741515 : Nat := 2948156879999209029857759

theorem tailTrace_5741515 : CollatzResearch.WordTrace tailWord_5741515 prefixEnd_5741515 2948156879999209029857759 := by
  unfold tailWord_5741515
  simp only [CollatzResearch.WordTrace]
  refine ⟨209410255794479202539729999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139606837196319468359819999 209410255794479202539729999)
  ·
    refine ⟨314115383691718803809594999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209410255794479202539729999 314115383691718803809594999)
    ·
      refine ⟨471173075537578205714392499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314115383691718803809594999 471173075537578205714392499)
      ·
        refine ⟨706759613306367308571588749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471173075537578205714392499 706759613306367308571588749)
        ·
          refine ⟨265034854989887740714345781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 706759613306367308571588749 265034854989887740714345781)
          ·
            refine ⟨24847017655301975691969917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 265034854989887740714345781 24847017655301975691969917)
            ·
              refine ⟨9317631620738240884488719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24847017655301975691969917 9317631620738240884488719)
              ·
                refine ⟨13976447431107361326733079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9317631620738240884488719 13976447431107361326733079)
                ·
                  refine ⟨20964671146661041990099619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13976447431107361326733079 20964671146661041990099619)
                  ·
                    refine ⟨31447006719991562985149429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20964671146661041990099619 31447006719991562985149429)
                    ·
                      refine ⟨2948156879999209029857759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31447006719991562985149429 2948156879999209029857759)
                      ·
                        rfl

theorem cell23_5741515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 5].length) (baseStart_5741515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741515 prefixEnd_5741515 := by exact prefixLift 5741515
  have htrace : WordTrace (prefixWord ++ tailWord_5741515) baseStart_5741515 baseEnd_5741515 := by
    simpa [prefixWord, tailWord_5741515, baseEnd_5741515] using wordTrace_append hprefix tailTrace_5741515
  have hstable : (prefixWord ++ tailWord_5741515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741515).length < 2 ^ (prefixWord ++ tailWord_5741515).sum := by decide
  have hdescent : baseEnd_5741515 < baseStart_5741515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741517 : List Nat := [1, 6, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5741517 : Nat := 118140960795 + 5741517 * 2 ^ 59
def prefixEnd_5741517 : Nat := 4983230072969 + 3 ^ 40 * 5741517 * 2
def baseEnd_5741517 : Nat := 982719302320172674010917

theorem tailTrace_5741517 : CollatzResearch.WordTrace tailWord_5741517 prefixEnd_5741517 982719302320172674010917 := by
  unfold tailWord_5741517
  simp only [CollatzResearch.WordTrace]
  refine ⟨209410328740471956881302805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139606885826981304587535203 209410328740471956881302805)
  ·
    refine ⟨9816109159709622978811069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 209410328740471956881302805 9816109159709622978811069)
    ·
      refine ⟨3681040934891108617054151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9816109159709622978811069 3681040934891108617054151)
      ·
        refine ⟨5521561402336662925581227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681040934891108617054151 5521561402336662925581227)
        ·
          refine ⟨8282342103504994388371841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521561402336662925581227 8282342103504994388371841)
          ·
            refine ⟨6211756577628745791278881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8282342103504994388371841 6211756577628745791278881)
            ·
              refine ⟨4658817433221559343459161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6211756577628745791278881 4658817433221559343459161)
              ·
                refine ⟨3494113074916169507594371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4658817433221559343459161 3494113074916169507594371)
                ·
                  refine ⟨5241169612374254261391557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494113074916169507594371 5241169612374254261391557)
                  ·
                    refine ⟨982719302320172674010917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241169612374254261391557 982719302320172674010917)
                    ·
                      rfl

theorem cell23_5741517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5741517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741517 prefixEnd_5741517 := by exact prefixLift 5741517
  have htrace : WordTrace (prefixWord ++ tailWord_5741517) baseStart_5741517 baseEnd_5741517 := by
    simpa [prefixWord, tailWord_5741517, baseEnd_5741517] using wordTrace_append hprefix tailTrace_5741517
  have hstable : (prefixWord ++ tailWord_5741517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741517).length < 2 ^ (prefixWord ++ tailWord_5741517).sum := by decide
  have hdescent : baseEnd_5741517 < baseStart_5741517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741518 : List Nat := [4, 1, 1, 1, 2, 14]
def baseStart_5741518 : Nat := 118140960795 + 5741518 * 2 ^ 59
def prefixEnd_5741518 : Nat := 4983230072969 + 3 ^ 40 * 5741518 * 2
def baseEnd_5741518 : Nat := 12132339178770257276215

theorem tailTrace_5741518 : CollatzResearch.WordTrace tailWord_5741518 prefixEnd_5741518 12132339178770257276215 := by
  unfold tailWord_5741518
  simp only [CollatzResearch.WordTrace]
  refine ⟨26176295651683541756511151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139606910142312222701392805 26176295651683541756511151)
  ·
    refine ⟨39264443477525312634766727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26176295651683541756511151 39264443477525312634766727)
    ·
      refine ⟨58896665216287968952150091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39264443477525312634766727 58896665216287968952150091)
      ·
        refine ⟨88344997824431953428225137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58896665216287968952150091 88344997824431953428225137)
        ·
          refine ⟨66258748368323965071168853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88344997824431953428225137 66258748368323965071168853)
          ·
            refine ⟨12132339178770257276215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 66258748368323965071168853 12132339178770257276215)
            ·
              rfl

theorem cell23_5741518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 14].length) (baseStart_5741518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741518 prefixEnd_5741518 := by exact prefixLift 5741518
  have htrace : WordTrace (prefixWord ++ tailWord_5741518) baseStart_5741518 baseEnd_5741518 := by
    simpa [prefixWord, tailWord_5741518, baseEnd_5741518] using wordTrace_append hprefix tailTrace_5741518
  have hstable : (prefixWord ++ tailWord_5741518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741518).length < 2 ^ (prefixWord ++ tailWord_5741518).sum := by decide
  have hdescent : baseEnd_5741518 < baseStart_5741518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741566 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5741566 : Nat := 118140960795 + 5741566 * 2 ^ 59
def prefixEnd_5741566 : Nat := 4983230072969 + 3 ^ 40 * 5741566 * 2
def baseEnd_5741566 : Nat := 2948183067512588330320025

theorem tailTrace_5741566 : CollatzResearch.WordTrace tailWord_5741566 prefixEnd_5741566 2948183067512588330320025 := by
  unfold tailWord_5741566
  simp only [CollatzResearch.WordTrace]
  refine ⟨26176514489661804781229569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139608077278196292166557701 26176514489661804781229569)
  ·
    refine ⟨19632385867246353585922177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26176514489661804781229569 19632385867246353585922177)
    ·
      refine ⟨14724289400434765189441633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19632385867246353585922177 14724289400434765189441633)
      ·
        refine ⟨11043217050326073892081225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14724289400434765189441633 11043217050326073892081225)
        ·
          refine ⟨8282412787744555419060919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11043217050326073892081225 8282412787744555419060919)
          ·
            refine ⟨12423619181616833128591379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8282412787744555419060919 12423619181616833128591379)
            ·
              refine ⟨18635428772425249692887069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12423619181616833128591379 18635428772425249692887069)
              ·
                refine ⟨6988285789659468634832651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18635428772425249692887069 6988285789659468634832651)
                ·
                  refine ⟨10482428684489202952248977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6988285789659468634832651 10482428684489202952248977)
                  ·
                    refine ⟨7861821513366902214186733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10482428684489202952248977 7861821513366902214186733)
                    ·
                      refine ⟨2948183067512588330320025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7861821513366902214186733 2948183067512588330320025)
                      ·
                        rfl

theorem cell23_5741566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5741566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741566 prefixEnd_5741566 := by exact prefixLift 5741566
  have htrace : WordTrace (prefixWord ++ tailWord_5741566) baseStart_5741566 baseEnd_5741566 := by
    simpa [prefixWord, tailWord_5741566, baseEnd_5741566] using wordTrace_append hprefix tailTrace_5741566
  have hstable : (prefixWord ++ tailWord_5741566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741566).length < 2 ^ (prefixWord ++ tailWord_5741566).sum := by decide
  have hdescent : baseEnd_5741566 < baseStart_5741566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741579 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 3]
def baseStart_5741579 : Nat := 118140960795 + 5741579 * 2 ^ 59
def prefixEnd_5741579 : Nat := 4983230072969 + 3 ^ 40 * 5741579 * 2
def baseEnd_5741579 : Nat := 2948189742761096779457465

theorem tailTrace_5741579 : CollatzResearch.WordTrace tailWord_5741579 prefixEnd_5741579 2948189742761096779457465 := by
  unfold tailWord_5741579
  simp only [CollatzResearch.WordTrace]
  refine ⟨209412590066247341470059791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139608393377498227646706527 209412590066247341470059791)
  ·
    refine ⟨314118885099371012205089687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209412590066247341470059791 314118885099371012205089687)
    ·
      refine ⟨471178327649056518307634531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314118885099371012205089687 471178327649056518307634531)
      ·
        refine ⟨706767491473584777461451797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471178327649056518307634531 706767491473584777461451797)
        ·
          refine ⟨33129726162824286443505553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 706767491473584777461451797 33129726162824286443505553)
          ·
            refine ⟨24847294622118214832629165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33129726162824286443505553 24847294622118214832629165)
            ·
              refine ⟨9317735483294330562235937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24847294622118214832629165 9317735483294330562235937)
              ·
                refine ⟨6988301612470747921676953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9317735483294330562235937 6988301612470747921676953)
                ·
                  refine ⟨5241226209353060941257715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6988301612470747921676953 5241226209353060941257715)
                  ·
                    refine ⟨7861839314029591411886573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241226209353060941257715 7861839314029591411886573)
                    ·
                      refine ⟨2948189742761096779457465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7861839314029591411886573 2948189742761096779457465)
                      ·
                        rfl

theorem cell23_5741579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 1, 3].length) (baseStart_5741579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741579 prefixEnd_5741579 := by exact prefixLift 5741579
  have htrace : WordTrace (prefixWord ++ tailWord_5741579) baseStart_5741579 baseEnd_5741579 := by
    simpa [prefixWord, tailWord_5741579, baseEnd_5741579] using wordTrace_append hprefix tailTrace_5741579
  have hstable : (prefixWord ++ tailWord_5741579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741579).length < 2 ^ (prefixWord ++ tailWord_5741579).sum := by decide
  have hdescent : baseEnd_5741579 < baseStart_5741579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741596 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_5741596 : Nat := 118140960795 + 5741596 * 2 ^ 59
def prefixEnd_5741596 : Nat := 4983230072969 + 3 ^ 40 * 5741596 * 2
def baseEnd_5741596 : Nat := 2948198471932223212944887

theorem tailTrace_5741596 : CollatzResearch.WordTrace tailWord_5741596 prefixEnd_5741596 2948198471932223212944887 := by
  unfold tailWord_5741596
  simp only [CollatzResearch.WordTrace]
  refine ⟨104706605053592876686714321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139608806738123835582285761 104706605053592876686714321)
  ·
    refine ⟨78529953790194657515035741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104706605053592876686714321 78529953790194657515035741)
    ·
      refine ⟨29448732671322996568138403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78529953790194657515035741 29448732671322996568138403)
      ·
        refine ⟨44173099006984494852207605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29448732671322996568138403 44173099006984494852207605)
        ·
          refine ⟨4141228031904796392394463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44173099006984494852207605 4141228031904796392394463)
          ·
            refine ⟨6211842047857194588591695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141228031904796392394463 6211842047857194588591695)
            ·
              refine ⟨9317763071785791882887543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6211842047857194588591695 9317763071785791882887543)
              ·
                refine ⟨13976644607678687824331315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9317763071785791882887543 13976644607678687824331315)
                ·
                  refine ⟨20964966911518031736496973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13976644607678687824331315 20964966911518031736496973)
                  ·
                    refine ⟨7861862591819261901186365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20964966911518031736496973 7861862591819261901186365)
                    ·
                      refine ⟨2948198471932223212944887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7861862591819261901186365 2948198471932223212944887)
                      ·
                        rfl

theorem cell23_5741596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_5741596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741596 prefixEnd_5741596 := by exact prefixLift 5741596
  have htrace : WordTrace (prefixWord ++ tailWord_5741596) baseStart_5741596 baseEnd_5741596 := by
    simpa [prefixWord, tailWord_5741596, baseEnd_5741596] using wordTrace_append hprefix tailTrace_5741596
  have hstable : (prefixWord ++ tailWord_5741596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741596).length < 2 ^ (prefixWord ++ tailWord_5741596).sum := by decide
  have hdescent : baseEnd_5741596 < baseStart_5741596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741605 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_5741605 : Nat := 118140960795 + 5741605 * 2 ^ 59
def prefixEnd_5741605 : Nat := 4983230072969 + 3 ^ 40 * 5741605 * 2
def baseEnd_5741605 : Nat := 2948203093258113677732345

theorem tailTrace_5741605 : CollatzResearch.WordTrace tailWord_5741605 prefixEnd_5741605 2948203093258113677732345 := by
  unfold tailWord_5741605
  simp only [CollatzResearch.WordTrace]
  refine ⟨209413538364153147910506269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139609025576102098607004179 209413538364153147910506269)
  ·
    refine ⟨78530076886557430466439851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209413538364153147910506269 78530076886557430466439851)
    ·
      refine ⟨117795115329836145699659777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78530076886557430466439851 117795115329836145699659777)
      ·
        refine ⟨88346336497377109274744833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117795115329836145699659777 88346336497377109274744833)
        ·
          refine ⟨66259752373032831956058625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88346336497377109274744833 66259752373032831956058625)
          ·
            refine ⟨49694814279774623967043969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66259752373032831956058625 49694814279774623967043969)
            ·
              refine ⟨37271110709830967975282977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49694814279774623967043969 37271110709830967975282977)
              ·
                refine ⟨27953333032373225981462233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37271110709830967975282977 27953333032373225981462233)
                ·
                  refine ⟨20964999774279919486096675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27953333032373225981462233 20964999774279919486096675)
                  ·
                    refine ⟨31447499661419879229145013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20964999774279919486096675 31447499661419879229145013)
                    ·
                      refine ⟨2948203093258113677732345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31447499661419879229145013 2948203093258113677732345)
                      ·
                        rfl

theorem cell23_5741605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_5741605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741605 prefixEnd_5741605 := by exact prefixLift 5741605
  have htrace : WordTrace (prefixWord ++ tailWord_5741605) baseStart_5741605 baseEnd_5741605 := by
    simpa [prefixWord, tailWord_5741605, baseEnd_5741605] using wordTrace_append hprefix tailTrace_5741605
  have hstable : (prefixWord ++ tailWord_5741605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741605).length < 2 ^ (prefixWord ++ tailWord_5741605).sum := by decide
  have hdescent : baseEnd_5741605 < baseStart_5741605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741622 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_5741622 : Nat := 118140960795 + 5741622 * 2 ^ 59
def prefixEnd_5741622 : Nat := 4983230072969 + 3 ^ 40 * 5741622 * 2
def baseEnd_5741622 : Nat := 2948211822429240111219767

theorem tailTrace_5741622 : CollatzResearch.WordTrace tailWord_5741622 prefixEnd_5741622 2948211822429240111219767 := by
  unfold tailWord_5741622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13088384900318222488367195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139609438936727706542583413 13088384900318222488367195)
  ·
    refine ⟨19632577350477333732550793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13088384900318222488367195 19632577350477333732550793)
    ·
      refine ⟨14724433012858000299413095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19632577350477333732550793 14724433012858000299413095)
      ·
        refine ⟨22086649519287000449119643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14724433012858000299413095 22086649519287000449119643)
        ·
          refine ⟨33129974278930500673679465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22086649519287000449119643 33129974278930500673679465)
          ·
            refine ⟨24847480709197875505259599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33129974278930500673679465 24847480709197875505259599)
            ·
              refine ⟨37271221063796813257889399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24847480709197875505259599 37271221063796813257889399)
              ·
                refine ⟨55906831595695219886834099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37271221063796813257889399 55906831595695219886834099)
                ·
                  refine ⟨83860247393542829830251149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55906831595695219886834099 83860247393542829830251149)
                  ·
                    refine ⟨31447592772578561186344181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83860247393542829830251149 31447592772578561186344181)
                    ·
                      refine ⟨2948211822429240111219767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31447592772578561186344181 2948211822429240111219767)
                      ·
                        rfl

theorem cell23_5741622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_5741622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741622 prefixEnd_5741622 := by exact prefixLift 5741622
  have htrace : WordTrace (prefixWord ++ tailWord_5741622) baseStart_5741622 baseEnd_5741622 := by
    simpa [prefixWord, tailWord_5741622, baseEnd_5741622] using wordTrace_append hprefix tailTrace_5741622
  have hstable : (prefixWord ++ tailWord_5741622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741622).length < 2 ^ (prefixWord ++ tailWord_5741622).sum := by decide
  have hdescent : baseEnd_5741622 < baseStart_5741622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741642 : List Nat := [3, 1, 2, 1, 1, 2, 2, 6, 5]
def baseStart_5741642 : Nat := 118140960795 + 5741642 * 2 ^ 59
def prefixEnd_5741642 : Nat := 4983230072969 + 3 ^ 40 * 5741642 * 2
def baseEnd_5741642 : Nat := 327580232449147781441075

theorem tailTrace_5741642 : CollatzResearch.WordTrace tailWord_5741642 prefixEnd_5741642 327580232449147781441075 := by
  unfold tailWord_5741642
  simp only [CollatzResearch.WordTrace]
  refine ⟨52353721966254775807400795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139609925243346068819735453 52353721966254775807400795)
  ·
    refine ⟨78530582949382163711101193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52353721966254775807400795 78530582949382163711101193)
    ·
      refine ⟨58897937212036622783325895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78530582949382163711101193 58897937212036622783325895)
      ·
        refine ⟨88346905818054934174988843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58897937212036622783325895 88346905818054934174988843)
        ·
          refine ⟨132520358727082401262483265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88346905818054934174988843 132520358727082401262483265)
          ·
            refine ⟨99390269045311800946862449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132520358727082401262483265 99390269045311800946862449)
            ·
              refine ⟨74542701783983850710146837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99390269045311800946862449 74542701783983850710146837)
              ·
                refine ⟨3494189146124243002038133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74542701783983850710146837 3494189146124243002038133)
                ·
                  refine ⟨327580232449147781441075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3494189146124243002038133 327580232449147781441075)
                  ·
                    rfl

theorem cell23_5741642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_5741642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741642 prefixEnd_5741642 := by exact prefixLift 5741642
  have htrace : WordTrace (prefixWord ++ tailWord_5741642) baseStart_5741642 baseEnd_5741642 := by
    simpa [prefixWord, tailWord_5741642, baseEnd_5741642] using wordTrace_append hprefix tailTrace_5741642
  have hstable : (prefixWord ++ tailWord_5741642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741642).length < 2 ^ (prefixWord ++ tailWord_5741642).sum := by decide
  have hdescent : baseEnd_5741642 < baseStart_5741642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741652 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_5741652 : Nat := 118140960795 + 5741652 * 2 ^ 59
def prefixEnd_5741652 : Nat := 4983230072969 + 3 ^ 40 * 5741652 * 2
def baseEnd_5741652 : Nat := 2948227226848874993844629

theorem tailTrace_5741652 : CollatzResearch.WordTrace tailWord_5741652 prefixEnd_5741652 2948227226848874993844629 := by
  unfold tailWord_5741652
  simp only [CollatzResearch.WordTrace]
  refine ⟨104707626297491437468733605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139610168396655249958311473 104707626297491437468733605)
  ·
    refine ⟨19632679930779644525387551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104707626297491437468733605 19632679930779644525387551)
    ·
      refine ⟨29449019896169466788081327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19632679930779644525387551 29449019896169466788081327)
      ·
        refine ⟨44173529844254200182121991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29449019896169466788081327 44173529844254200182121991)
        ·
          refine ⟨66260294766381300273182987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44173529844254200182121991 66260294766381300273182987)
          ·
            refine ⟨99390442149571950409774481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66260294766381300273182987 99390442149571950409774481)
            ·
              refine ⟨74542831612178962807330861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99390442149571950409774481 74542831612178962807330861)
              ·
                refine ⟨27953561854567111052749073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74542831612178962807330861 27953561854567111052749073)
                ·
                  refine ⟨20965171390925333289561805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27953561854567111052749073 20965171390925333289561805)
                  ·
                    refine ⟨7861939271596999983585677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20965171390925333289561805 7861939271596999983585677)
                    ·
                      refine ⟨2948227226848874993844629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7861939271596999983585677 2948227226848874993844629)
                      ·
                        rfl

theorem cell23_5741652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_5741652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741652 prefixEnd_5741652 := by exact prefixLift 5741652
  have htrace : WordTrace (prefixWord ++ tailWord_5741652) baseStart_5741652 baseEnd_5741652 := by
    simpa [prefixWord, tailWord_5741652, baseEnd_5741652] using wordTrace_append hprefix tailTrace_5741652
  have hstable : (prefixWord ++ tailWord_5741652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741652).length < 2 ^ (prefixWord ++ tailWord_5741652).sum := by decide
  have hdescent : baseEnd_5741652 < baseStart_5741652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741655 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 6, 5]
def baseStart_5741655 : Nat := 118140960795 + 5741655 * 2 ^ 59
def prefixEnd_5741655 : Nat := 4983230072969 + 3 ^ 40 * 5741655 * 2
def baseEnd_5741655 : Nat := 982742922430279494035705

theorem tailTrace_5741655 : CollatzResearch.WordTrace tailWord_5741655 prefixEnd_5741655 982742922430279494035705 := by
  unfold tailWord_5741655
  simp only [CollatzResearch.WordTrace]
  refine ⟨209415362013972006449826419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139610241342648004299884279 209415362013972006449826419)
  ·
    refine ⟨314123043020958009674739629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209415362013972006449826419 314123043020958009674739629)
    ·
      refine ⟨117796141132859253628027361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314123043020958009674739629 117796141132859253628027361)
      ·
        refine ⟨88347105849644440221020521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117796141132859253628027361 88347105849644440221020521)
        ·
          refine ⟨66260329387233330165765391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88347105849644440221020521 66260329387233330165765391)
          ·
            refine ⟨99390494080849995248648087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66260329387233330165765391 99390494080849995248648087)
            ·
              refine ⟨149085741121274992872972131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99390494080849995248648087 149085741121274992872972131)
              ·
                refine ⟨223628611681912489309458197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149085741121274992872972131 223628611681912489309458197)
                ·
                  refine ⟨10482591172589647936380853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223628611681912489309458197 10482591172589647936380853)
                  ·
                    refine ⟨982742922430279494035705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10482591172589647936380853 982742922430279494035705)
                    ·
                      rfl

theorem cell23_5741655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_5741655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741655 prefixEnd_5741655 := by exact prefixLift 5741655
  have htrace : WordTrace (prefixWord ++ tailWord_5741655) baseStart_5741655 baseEnd_5741655 := by
    simpa [prefixWord, tailWord_5741655, baseEnd_5741655] using wordTrace_append hprefix tailTrace_5741655
  have hstable : (prefixWord ++ tailWord_5741655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741655).length < 2 ^ (prefixWord ++ tailWord_5741655).sum := by decide
  have hdescent : baseEnd_5741655 < baseStart_5741655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741692 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_5741692 : Nat := 118140960795 + 5741692 * 2 ^ 59
def prefixEnd_5741692 : Nat := 4983230072969 + 3 ^ 40 * 5741692 * 2
def baseEnd_5741692 : Nat := 2948247766075054837344445

theorem tailTrace_5741692 : CollatzResearch.WordTrace tailWord_5741692 prefixEnd_5741692 2948247766075054837344445 := by
  unfold tailWord_5741692
  simp only [CollatzResearch.WordTrace]
  refine ⟨104708355757418980884461665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139611141009891974512615553 104708355757418980884461665)
  ·
    refine ⟨78531266818064235663346249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104708355757418980884461665 78531266818064235663346249)
    ·
      refine ⟨58898450113548176747509687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78531266818064235663346249 58898450113548176747509687)
      ·
        refine ⟨88347675170322265121264531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58898450113548176747509687 88347675170322265121264531)
        ·
          refine ⟨132521512755483397681896797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88347675170322265121264531 132521512755483397681896797)
          ·
            refine ⟨49695567283306274130711299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132521512755483397681896797 49695567283306274130711299)
            ·
              refine ⟨74543350924959411196066949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49695567283306274130711299 74543350924959411196066949)
              ·
                refine ⟨13976878298429889599262553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74543350924959411196066949 13976878298429889599262553)
                ·
                  refine ⟨10482658723822417199446915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13976878298429889599262553 10482658723822417199446915)
                  ·
                    refine ⟨15723988085733625799170373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10482658723822417199446915 15723988085733625799170373)
                    ·
                      refine ⟨2948247766075054837344445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15723988085733625799170373 2948247766075054837344445)
                      ·
                        rfl

theorem cell23_5741692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_5741692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741692 prefixEnd_5741692 := by exact prefixLift 5741692
  have htrace : WordTrace (prefixWord ++ tailWord_5741692) baseStart_5741692 baseEnd_5741692 := by
    simpa [prefixWord, tailWord_5741692, baseEnd_5741692] using wordTrace_append hprefix tailTrace_5741692
  have hstable : (prefixWord ++ tailWord_5741692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741692).length < 2 ^ (prefixWord ++ tailWord_5741692).sum := by decide
  have hdescent : baseEnd_5741692 < baseStart_5741692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741719 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 3, 4]
def baseStart_5741719 : Nat := 118140960795 + 5741719 * 2 ^ 59
def prefixEnd_5741719 : Nat := 4983230072969 + 3 ^ 40 * 5741719 * 2
def baseEnd_5741719 : Nat := 982753876684242077235607

theorem tailTrace_5741719 : CollatzResearch.WordTrace tailWord_5741719 prefixEnd_5741719 982753876684242077235607 := by
  unfold tailWord_5741719
  simp only [CollatzResearch.WordTrace]
  refine ⟨209417696285740145380156211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139611797523826763586770807 209417696285740145380156211)
  ·
    refine ⟨314126544428610218070234317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209417696285740145380156211 314126544428610218070234317)
    ·
      refine ⟨117797454160728831776337869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 314126544428610218070234317 117797454160728831776337869)
      ·
        refine ⟨44174045310273311916126701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117797454160728831776337869 44174045310273311916126701)
        ·
          refine ⟨16565266991352491968547513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44174045310273311916126701 16565266991352491968547513)
          ·
            refine ⟨12423950243514368976410635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16565266991352491968547513 12423950243514368976410635)
            ·
              refine ⟨18635925365271553464615953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12423950243514368976410635 18635925365271553464615953)
              ·
                refine ⟨13976944023953665098461965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18635925365271553464615953 13976944023953665098461965)
                ·
                  refine ⟨5241354008982624411923237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13976944023953665098461965 5241354008982624411923237)
                  ·
                    refine ⟨982753876684242077235607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241354008982624411923237 982753876684242077235607)
                    ·
                      rfl

theorem cell23_5741719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_5741719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741719 prefixEnd_5741719 := by exact prefixLift 5741719
  have htrace : WordTrace (prefixWord ++ tailWord_5741719) baseStart_5741719 baseEnd_5741719 := by
    simpa [prefixWord, tailWord_5741719, baseEnd_5741719] using wordTrace_append hprefix tailTrace_5741719
  have hstable : (prefixWord ++ tailWord_5741719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741719).length < 2 ^ (prefixWord ++ tailWord_5741719).sum := by decide
  have hdescent : baseEnd_5741719 < baseStart_5741719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741726 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_5741726 : Nat := 118140960795 + 5741726 * 2 ^ 59
def prefixEnd_5741726 : Nat := 4983230072969 + 3 ^ 40 * 5741726 * 2
def baseEnd_5741726 : Nat := 2948265224417307704319289

theorem tailTrace_5741726 : CollatzResearch.WordTrace tailWord_5741726 prefixEnd_5741726 2948265224417307704319289 := by
  unfold tailWord_5741726
  simp only [CollatzResearch.WordTrace]
  refine ⟨26177243949589348196957629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139611967731143190383774021 26177243949589348196957629)
  ·
    refine ⟨9816466481096005573859111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26177243949589348196957629 9816466481096005573859111)
    ·
      refine ⟨14724699721644008360788667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9816466481096005573859111 14724699721644008360788667)
      ·
        refine ⟨22087049582466012541183001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14724699721644008360788667 22087049582466012541183001)
        ·
          refine ⟨16565287186849509405887251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22087049582466012541183001 16565287186849509405887251)
          ·
            refine ⟨24847930780274264108830877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16565287186849509405887251 24847930780274264108830877)
            ·
              refine ⟨9317974042602849040811579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24847930780274264108830877 9317974042602849040811579)
              ·
                refine ⟨13976961063904273561217369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9317974042602849040811579 13976961063904273561217369)
                ·
                  refine ⟨10482720797928205170913027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13976961063904273561217369 10482720797928205170913027)
                  ·
                    refine ⟨15724081196892307756369541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10482720797928205170913027 15724081196892307756369541)
                    ·
                      refine ⟨2948265224417307704319289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15724081196892307756369541 2948265224417307704319289)
                      ·
                        rfl

theorem cell23_5741726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_5741726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741726 prefixEnd_5741726 := by exact prefixLift 5741726
  have htrace : WordTrace (prefixWord ++ tailWord_5741726) baseStart_5741726 baseEnd_5741726 := by
    simpa [prefixWord, tailWord_5741726, baseEnd_5741726] using wordTrace_append hprefix tailTrace_5741726
  have hstable : (prefixWord ++ tailWord_5741726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741726).length < 2 ^ (prefixWord ++ tailWord_5741726).sum := by decide
  have hdescent : baseEnd_5741726 < baseStart_5741726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741755 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7]
def baseStart_5741755 : Nat := 118140960795 + 5741755 * 2 ^ 59
def prefixEnd_5741755 : Nat := 4983230072969 + 3 ^ 40 * 5741755 * 2
def baseEnd_5741755 : Nat := 2948280115356288090856655

theorem tailTrace_5741755 : CollatzResearch.WordTrace tailWord_5741755 prefixEnd_5741755 2948280115356288090856655 := by
  unfold tailWord_5741755
  simp only [CollatzResearch.WordTrace]
  refine ⟨209419009313609723528466719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139612672875739815685644479 209419009313609723528466719)
  ·
    refine ⟨314128513970414585292700079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209419009313609723528466719 314128513970414585292700079)
    ·
      refine ⟨471192770955621877939050119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314128513970414585292700079 471192770955621877939050119)
      ·
        refine ⟨706789156433432816908575179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471192770955621877939050119 706789156433432816908575179)
        ·
          refine ⟨1060183734650149225362862769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706789156433432816908575179 1060183734650149225362862769)
          ·
            refine ⟨795137800987611919022147077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060183734650149225362862769 795137800987611919022147077)
            ·
              refine ⟨149088337685177234816652577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 795137800987611919022147077 149088337685177234816652577)
              ·
                refine ⟨111816253263882926112489433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149088337685177234816652577 111816253263882926112489433)
                ·
                  refine ⟨83862189947912194584367075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111816253263882926112489433 83862189947912194584367075)
                  ·
                    refine ⟨125793284921868291876550613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83862189947912194584367075 125793284921868291876550613)
                    ·
                      refine ⟨2948280115356288090856655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125793284921868291876550613 2948280115356288090856655)
                      ·
                        rfl

theorem cell23_5741755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_5741755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741755 prefixEnd_5741755 := by exact prefixLift 5741755
  have htrace : WordTrace (prefixWord ++ tailWord_5741755) baseStart_5741755 baseEnd_5741755 := by
    simpa [prefixWord, tailWord_5741755, baseEnd_5741755] using wordTrace_append hprefix tailTrace_5741755
  have hstable : (prefixWord ++ tailWord_5741755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741755).length < 2 ^ (prefixWord ++ tailWord_5741755).sum := by decide
  have hdescent : baseEnd_5741755 < baseStart_5741755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741759 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 3]
def baseStart_5741759 : Nat := 118140960795 + 5741759 * 2 ^ 59
def prefixEnd_5741759 : Nat := 4983230072969 + 3 ^ 40 * 5741759 * 2
def baseEnd_5741759 : Nat := 2948282169278906075206637

theorem tailTrace_5741759 : CollatzResearch.WordTrace tailWord_5741759 prefixEnd_5741759 2948282169278906075206637 := by
  unfold tailWord_5741759
  simp only [CollatzResearch.WordTrace]
  refine ⟨209419155205595232211612331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139612770137063488141074887 209419155205595232211612331)
  ·
    refine ⟨314128732808392848317418497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209419155205595232211612331 314128732808392848317418497)
    ·
      refine ⟨235596549606294636238063873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314128732808392848317418497 235596549606294636238063873)
      ·
        refine ⟨176697412204720977178547905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235596549606294636238063873 176697412204720977178547905)
        ·
          refine ⟨132523059153540732883910929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176697412204720977178547905 132523059153540732883910929)
          ·
            refine ⟨99392294365155549662933197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132523059153540732883910929 99392294365155549662933197)
            ·
              refine ⟨37272110386933331123599949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99392294365155549662933197 37272110386933331123599949)
              ·
                refine ⟨13977041395099999171349981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37272110386933331123599949 13977041395099999171349981)
                ·
                  refine ⟨5241390523162499689256243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13977041395099999171349981 5241390523162499689256243)
                  ·
                    refine ⟨7862085784743749533884365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241390523162499689256243 7862085784743749533884365)
                    ·
                      refine ⟨2948282169278906075206637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862085784743749533884365 2948282169278906075206637)
                      ·
                        rfl

theorem cell23_5741759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_5741759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741759 prefixEnd_5741759 := by exact prefixLift 5741759
  have htrace : WordTrace (prefixWord ++ tailWord_5741759) baseStart_5741759 baseEnd_5741759 := by
    simpa [prefixWord, tailWord_5741759, baseEnd_5741759] using wordTrace_append hprefix tailTrace_5741759
  have hstable : (prefixWord ++ tailWord_5741759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741759).length < 2 ^ (prefixWord ++ tailWord_5741759).sum := by decide
  have hdescent : baseEnd_5741759 < baseStart_5741759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741793 : List Nat := [1, 2, 3, 1, 3, 2, 3, 3, 1, 1, 3]
def baseStart_5741793 : Nat := 118140960795 + 5741793 * 2 ^ 59
def prefixEnd_5741793 : Nat := 4983230072969 + 3 ^ 40 * 5741793 * 2
def baseEnd_5741793 : Nat := 2948299627621158942181481

theorem tailTrace_5741793 : CollatzResearch.WordTrace tailWord_5741793 prefixEnd_5741793 2948299627621158942181481 := by
  unfold tailWord_5741793
  simp only [CollatzResearch.WordTrace]
  refine ⟨209420395287472056018350033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139613596858314704012233355 209420395287472056018350033)
  ·
    refine ⟨157065296465604042013762525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209420395287472056018350033 157065296465604042013762525)
    ·
      refine ⟨58899486174601515755160947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157065296465604042013762525 58899486174601515755160947)
      ·
        refine ⟨88349229261902273632741421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58899486174601515755160947 88349229261902273632741421)
        ·
          refine ⟨33130960973213352612278033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88349229261902273632741421 33130960973213352612278033)
          ·
            refine ⟨24848220729910014459208525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33130960973213352612278033 24848220729910014459208525)
            ·
              refine ⟨9318082773716255422203197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24848220729910014459208525 9318082773716255422203197)
              ·
                refine ⟨3494281040143595783326199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9318082773716255422203197 3494281040143595783326199)
                ·
                  refine ⟨5241421560215393674989299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3494281040143595783326199 5241421560215393674989299)
                  ·
                    refine ⟨7862132340323090512483949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241421560215393674989299 7862132340323090512483949)
                    ·
                      refine ⟨2948299627621158942181481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862132340323090512483949 2948299627621158942181481)
                      ·
                        rfl

theorem cell23_5741793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_5741793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741793 prefixEnd_5741793 := by exact prefixLift 5741793
  have htrace : WordTrace (prefixWord ++ tailWord_5741793) baseStart_5741793 baseEnd_5741793 := by
    simpa [prefixWord, tailWord_5741793, baseEnd_5741793] using wordTrace_append hprefix tailTrace_5741793
  have hstable : (prefixWord ++ tailWord_5741793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741793).length < 2 ^ (prefixWord ++ tailWord_5741793).sum := by decide
  have hdescent : baseEnd_5741793 < baseStart_5741793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741809 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 2, 4]
def baseStart_5741809 : Nat := 118140960795 + 5741809 * 2 ^ 59
def prefixEnd_5741809 : Nat := 4983230072969 + 3 ^ 40 * 5741809 * 2
def baseEnd_5741809 : Nat := 982769281103876959860469

theorem tailTrace_5741809 : CollatzResearch.WordTrace tailWord_5741809 prefixEnd_5741809 982769281103876959860469 := by
  unfold tailWord_5741809
  simp only [CollatzResearch.WordTrace]
  refine ⟨209420978855414090750932481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139613985903609393833954987 209420978855414090750932481)
  ·
    refine ⟨157065734141560568063199361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209420978855414090750932481 157065734141560568063199361)
    ·
      refine ⟨117799300606170426047399521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157065734141560568063199361 117799300606170426047399521)
      ·
        refine ⟨88349475454627819535549641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117799300606170426047399521 88349475454627819535549641)
        ·
          refine ⟨66262106590970864651662231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88349475454627819535549641 66262106590970864651662231)
          ·
            refine ⟨99393159886456296977493347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66262106590970864651662231 99393159886456296977493347)
            ·
              refine ⟨149089739829684445466240021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99393159886456296977493347 149089739829684445466240021)
              ·
                refine ⟨6988581554516458381230001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 149089739829684445466240021 6988581554516458381230001)
                ·
                  refine ⟨5241436165887343785922501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6988581554516458381230001 5241436165887343785922501)
                  ·
                    refine ⟨982769281103876959860469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5241436165887343785922501 982769281103876959860469)
                    ·
                      rfl

theorem cell23_5741809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_5741809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741809 prefixEnd_5741809 := by exact prefixLift 5741809
  have htrace : WordTrace (prefixWord ++ tailWord_5741809) baseStart_5741809 baseEnd_5741809 := by
    simpa [prefixWord, tailWord_5741809, baseEnd_5741809] using wordTrace_append hprefix tailTrace_5741809
  have hstable : (prefixWord ++ tailWord_5741809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741809).length < 2 ^ (prefixWord ++ tailWord_5741809).sum := by decide
  have hdescent : baseEnd_5741809 < baseStart_5741809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741810 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_5741810 : Nat := 118140960795 + 5741810 * 2 ^ 59
def prefixEnd_5741810 : Nat := 4983230072969 + 3 ^ 40 * 5741810 * 2
def baseEnd_5741810 : Nat := 2948308356792285375668903

theorem tailTrace_5741810 : CollatzResearch.WordTrace tailWord_5741810 prefixEnd_5741810 2948308356792285375668903 := by
  unfold tailWord_5741810
  simp only [CollatzResearch.WordTrace]
  refine ⟨52355253832102616980429721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139614010218940311947812589 52355253832102616980429721)
  ·
    refine ⟨39266440374076962735322291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52355253832102616980429721 39266440374076962735322291)
    ·
      refine ⟨58899660561115444102983437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39266440374076962735322291 58899660561115444102983437)
      ·
        refine ⟨22087372710418291538618789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58899660561115444102983437 22087372710418291538618789)
        ·
          refine ⟨4141382383203429663491023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22087372710418291538618789 4141382383203429663491023)
          ·
            refine ⟨6212073574805144495236535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141382383203429663491023 6212073574805144495236535)
            ·
              refine ⟨9318110362207716742854803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6212073574805144495236535 9318110362207716742854803)
              ·
                refine ⟨13977165543311575114282205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9318110362207716742854803 13977165543311575114282205)
                ·
                  refine ⟨5241437078741840667855827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13977165543311575114282205 5241437078741840667855827)
                  ·
                    refine ⟨7862155618112761001783741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241437078741840667855827 7862155618112761001783741)
                    ·
                      refine ⟨2948308356792285375668903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862155618112761001783741 2948308356792285375668903)
                      ·
                        rfl

theorem cell23_5741810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_5741810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741810 prefixEnd_5741810 := by exact prefixLift 5741810
  have htrace : WordTrace (prefixWord ++ tailWord_5741810) baseStart_5741810 baseEnd_5741810 := by
    simpa [prefixWord, tailWord_5741810, baseEnd_5741810] using wordTrace_append hprefix tailTrace_5741810
  have hstable : (prefixWord ++ tailWord_5741810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741810).length < 2 ^ (prefixWord ++ tailWord_5741810).sum := by decide
  have hdescent : baseEnd_5741810 < baseStart_5741810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741836 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_5741836 : Nat := 118140960795 + 5741836 * 2 ^ 59
def prefixEnd_5741836 : Nat := 4983230072969 + 3 ^ 40 * 5741836 * 2
def baseEnd_5741836 : Nat := 2948321707289302273943783

theorem tailTrace_5741836 : CollatzResearch.WordTrace tailWord_5741836 prefixEnd_5741836 2948321707289302273943783 := by
  unfold tailWord_5741836
  simp only [CollatzResearch.WordTrace]
  refine ⟨104710981813158137181082681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139614642417544182908110241 104710981813158137181082681)
  ·
    refine ⟨78533236359868602885812011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104710981813158137181082681 78533236359868602885812011)
    ·
      refine ⟨117799854539802904328718017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78533236359868602885812011 117799854539802904328718017)
      ·
        refine ⟨88349890904852178246538513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117799854539802904328718017 88349890904852178246538513)
        ·
          refine ⟨66262418178639133684903885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88349890904852178246538513 66262418178639133684903885)
          ·
            refine ⟨24848406816989675131838957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66262418178639133684903885 24848406816989675131838957)
            ·
              refine ⟨9318152556371128174439609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24848406816989675131838957 9318152556371128174439609)
              ·
                refine ⟨6988614417278346130829707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9318152556371128174439609 6988614417278346130829707)
                ·
                  refine ⟨10482921625917519196244561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6988614417278346130829707 10482921625917519196244561)
                  ·
                    refine ⟨7862191219438139397183421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10482921625917519196244561 7862191219438139397183421)
                    ·
                      refine ⟨2948321707289302273943783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862191219438139397183421 2948321707289302273943783)
                      ·
                        rfl

theorem cell23_5741836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_5741836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741836 prefixEnd_5741836 := by exact prefixLift 5741836
  have htrace : WordTrace (prefixWord ++ tailWord_5741836) baseStart_5741836 baseEnd_5741836 := by
    simpa [prefixWord, tailWord_5741836, baseEnd_5741836] using wordTrace_append hprefix tailTrace_5741836
  have hstable : (prefixWord ++ tailWord_5741836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741836).length < 2 ^ (prefixWord ++ tailWord_5741836).sum := by decide
  have hdescent : baseEnd_5741836 < baseStart_5741836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741872 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_5741872 : Nat := 118140960795 + 5741872 * 2 ^ 59
def prefixEnd_5741872 : Nat := 4983230072969 + 3 ^ 40 * 5741872 * 2
def baseEnd_5741872 : Nat := 2948340192592864133093617

theorem tailTrace_5741872 : CollatzResearch.WordTrace tailWord_5741872 prefixEnd_5741872 2948340192592864133093617 := by
  unfold tailWord_5741872
  simp only [CollatzResearch.WordTrace]
  refine ⟨104711638327092926255237935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139615517769457235006983913 104711638327092926255237935)
  ·
    refine ⟨157067457490639389382856903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104711638327092926255237935 157067457490639389382856903)
    ·
      refine ⟨235601186235959084074285355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157067457490639389382856903 235601186235959084074285355)
      ·
        refine ⟨353401779353938626111428033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235601186235959084074285355 353401779353938626111428033)
        ·
          refine ⟨265051334515453969583571025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353401779353938626111428033 265051334515453969583571025)
          ·
            refine ⟨198788500886590477187678269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265051334515453969583571025 198788500886590477187678269)
            ·
              refine ⟨74545687832471428945379351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198788500886590477187678269 74545687832471428945379351)
              ·
                refine ⟨111818531748707143418069027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74545687832471428945379351 111818531748707143418069027)
                ·
                  refine ⟨167727797623060715127103541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111818531748707143418069027 167727797623060715127103541)
                  ·
                    refine ⟨15724481027161942043165957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 167727797623060715127103541 15724481027161942043165957)
                    ·
                      refine ⟨2948340192592864133093617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15724481027161942043165957 2948340192592864133093617)
                      ·
                        rfl

theorem cell23_5741872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_5741872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741872 prefixEnd_5741872 := by exact prefixLift 5741872
  have htrace : WordTrace (prefixWord ++ tailWord_5741872) baseStart_5741872 baseEnd_5741872 := by
    simpa [prefixWord, tailWord_5741872, baseEnd_5741872] using wordTrace_append hprefix tailTrace_5741872
  have hstable : (prefixWord ++ tailWord_5741872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741872).length < 2 ^ (prefixWord ++ tailWord_5741872).sum := by decide
  have hdescent : baseEnd_5741872 < baseStart_5741872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741912 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 9]
def baseStart_5741912 : Nat := 118140960795 + 5741912 * 2 ^ 59
def prefixEnd_5741912 : Nat := 4983230072969 + 3 ^ 40 * 5741912 * 2
def baseEnd_5741912 : Nat := 327595636868782664065937

theorem tailTrace_5741912 : CollatzResearch.WordTrace tailWord_5741912 prefixEnd_5741912 327595636868782664065937 := by
  unfold tailWord_5741912
  simp only [CollatzResearch.WordTrace]
  refine ⟨104712367787020469670965995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139616490382693959561287993 104712367787020469670965995)
  ·
    refine ⟨157068551680530704506448993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104712367787020469670965995 157068551680530704506448993)
    ·
      refine ⟨117801413760398028379836745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157068551680530704506448993 117801413760398028379836745)
      ·
        refine ⟨88351060320298521284877559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117801413760398028379836745 88351060320298521284877559)
        ·
          refine ⟨132526590480447781927316339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88351060320298521284877559 132526590480447781927316339)
          ·
            refine ⟨198789885720671672890974509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132526590480447781927316339 198789885720671672890974509)
            ·
              refine ⟨74546207145251877334115441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198789885720671672890974509 74546207145251877334115441)
              ·
                refine ⟨55909655358938908000586581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74546207145251877334115441 55909655358938908000586581)
                ·
                  refine ⟨327595636868782664065937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55909655358938908000586581 327595636868782664065937)
                  ·
                    rfl

theorem cell23_5741912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 9].length) (baseStart_5741912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741912 prefixEnd_5741912 := by exact prefixLift 5741912
  have htrace : WordTrace (prefixWord ++ tailWord_5741912) baseStart_5741912 baseEnd_5741912 := by
    simpa [prefixWord, tailWord_5741912, baseEnd_5741912] using wordTrace_append hprefix tailTrace_5741912
  have hstable : (prefixWord ++ tailWord_5741912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741912).length < 2 ^ (prefixWord ++ tailWord_5741912).sum := by decide
  have hdescent : baseEnd_5741912 < baseStart_5741912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741917 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5741917 : Nat := 118140960795 + 5741917 * 2 ^ 59
def prefixEnd_5741917 : Nat := 4983230072969 + 3 ^ 40 * 5741917 * 2
def baseEnd_5741917 : Nat := 2948363299222316457030911

theorem tailTrace_5741917 : CollatzResearch.WordTrace tailWord_5741917 prefixEnd_5741917 2948363299222316457030911 := by
  unfold tailWord_5741917
  simp only [CollatzResearch.WordTrace]
  refine ⟨209424917939022825195864005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139616611959348550130576003 209424917939022825195864005)
  ·
    refine ⟨39267172113566779724224501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209424917939022825195864005 39267172113566779724224501)
    ·
      refine ⟨3681297385646885599146047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39267172113566779724224501 3681297385646885599146047)
      ·
        refine ⟨5521946078470328398719071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681297385646885599146047 5521946078470328398719071)
        ·
          refine ⟨8282919117705492598078607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5521946078470328398719071 8282919117705492598078607)
          ·
            refine ⟨12424378676558238897117911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8282919117705492598078607 12424378676558238897117911)
            ·
              refine ⟨18636568014837358345676867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12424378676558238897117911 18636568014837358345676867)
              ·
                refine ⟨27954852022256037518515301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18636568014837358345676867 27954852022256037518515301)
                ·
                  refine ⟨5241534754173007034721619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27954852022256037518515301 5241534754173007034721619)
                  ·
                    refine ⟨7862302131259510552082429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5241534754173007034721619 7862302131259510552082429)
                    ·
                      refine ⟨2948363299222316457030911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862302131259510552082429 2948363299222316457030911)
                      ·
                        rfl

theorem cell23_5741917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5741917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741917 prefixEnd_5741917 := by exact prefixLift 5741917
  have htrace : WordTrace (prefixWord ++ tailWord_5741917) baseStart_5741917 baseEnd_5741917 := by
    simpa [prefixWord, tailWord_5741917, baseEnd_5741917] using wordTrace_append hprefix tailTrace_5741917
  have hstable : (prefixWord ++ tailWord_5741917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741917).length < 2 ^ (prefixWord ++ tailWord_5741917).sum := by decide
  have hdescent : baseEnd_5741917 < baseStart_5741917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741923 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 4, 2, 2]
def baseStart_5741923 : Nat := 118140960795 + 5741923 * 2 ^ 59
def prefixEnd_5741923 : Nat := 4983230072969 + 3 ^ 40 * 5741923 * 2
def baseEnd_5741923 : Nat := 2948366380106243433555883

theorem tailTrace_5741923 : CollatzResearch.WordTrace tailWord_5741923 prefixEnd_5741923 2948366380106243433555883 := by
  unfold tailWord_5741923
  simp only [CollatzResearch.WordTrace]
  refine ⟨209425136777001088220582423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139616757851334058813721615 209425136777001088220582423)
  ·
    refine ⟨314137705165501632330873635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209425136777001088220582423 314137705165501632330873635)
    ·
      refine ⟨471206557748252448496310453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314137705165501632330873635 471206557748252448496310453)
      ·
        refine ⟨44175614788898667046529105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 471206557748252448496310453 44175614788898667046529105)
        ·
          refine ⟨33131711091674000284896829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44175614788898667046529105 33131711091674000284896829)
          ·
            refine ⟨12424391659377750106836311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33131711091674000284896829 12424391659377750106836311)
            ·
              refine ⟨18636587489066625160254467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12424391659377750106836311 18636587489066625160254467)
              ·
                refine ⟨27954881233599937740381701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18636587489066625160254467 27954881233599937740381701)
                ·
                  refine ⟨5241540231299988326321569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27954881233599937740381701 5241540231299988326321569)
                  ·
                    refine ⟨3931155173474991244741177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5241540231299988326321569 3931155173474991244741177)
                    ·
                      refine ⟨2948366380106243433555883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931155173474991244741177 2948366380106243433555883)
                      ·
                        rfl

theorem cell23_5741923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_5741923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741923 prefixEnd_5741923 := by exact prefixLift 5741923
  have htrace : WordTrace (prefixWord ++ tailWord_5741923) baseStart_5741923 baseEnd_5741923 := by
    simpa [prefixWord, tailWord_5741923, baseEnd_5741923] using wordTrace_append hprefix tailTrace_5741923
  have hstable : (prefixWord ++ tailWord_5741923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741923).length < 2 ^ (prefixWord ++ tailWord_5741923).sum := by decide
  have hdescent : baseEnd_5741923 < baseStart_5741923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741959 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 1, 7]
def baseStart_5741959 : Nat := 118140960795 + 5741959 * 2 ^ 59
def prefixEnd_5741959 : Nat := 4983230072969 + 3 ^ 40 * 5741959 * 2
def baseEnd_5741959 : Nat := 982794955136601764235239

theorem tailTrace_5741959 : CollatzResearch.WordTrace tailWord_5741959 prefixEnd_5741959 982794955136601764235239 := by
  unfold tailWord_5741959
  simp only [CollatzResearch.WordTrace]
  refine ⟨209426449804870666368892931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139617633203247110912595287 209426449804870666368892931)
  ·
    refine ⟨314139674707305999553339397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209426449804870666368892931 314139674707305999553339397)
    ·
      refine ⟨58901189007619874916251137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 314139674707305999553339397 58901189007619874916251137)
      ·
        refine ⟨44175891755714906187188353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58901189007619874916251137 44175891755714906187188353)
        ·
          refine ⟨33131918816786179640391265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44175891755714906187188353 33131918816786179640391265)
          ·
            refine ⟨24848939112589634730293449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33131918816786179640391265 24848939112589634730293449)
            ·
              refine ⟨18636704334442226047720087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24848939112589634730293449 18636704334442226047720087)
              ·
                refine ⟨27955056501663339071580131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18636704334442226047720087 27955056501663339071580131)
                ·
                  refine ⟨41932584752495008607370197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27955056501663339071580131 41932584752495008607370197)
                  ·
                    refine ⟨982794955136601764235239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41932584752495008607370197 982794955136601764235239)
                    ·
                      rfl

theorem cell23_5741959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_5741959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741959 prefixEnd_5741959 := by exact prefixLift 5741959
  have htrace : WordTrace (prefixWord ++ tailWord_5741959) baseStart_5741959 baseEnd_5741959 := by
    simpa [prefixWord, tailWord_5741959, baseEnd_5741959] using wordTrace_append hprefix tailTrace_5741959
  have hstable : (prefixWord ++ tailWord_5741959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741959).length < 2 ^ (prefixWord ++ tailWord_5741959).sum := by decide
  have hdescent : baseEnd_5741959 < baseStart_5741959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741980 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 7]
def baseStart_5741980 : Nat := 118140960795 + 5741980 * 2 ^ 59
def prefixEnd_5741980 : Nat := 4983230072969 + 3 ^ 40 * 5741980 * 2
def baseEnd_5741980 : Nat := 327599516500394412282569

theorem tailTrace_5741980 : CollatzResearch.WordTrace tailWord_5741980 prefixEnd_5741980 327599516500394412282569 := by
  unfold tailWord_5741980
  simp only [CollatzResearch.WordTrace]
  refine ⟨104713607868897293477703697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139618143825196391303604929 104713607868897293477703697)
  ·
    refine ⟨78535205901672970108277773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104713607868897293477703697 78535205901672970108277773)
    ·
      refine ⟨29450702213127363790604165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78535205901672970108277773 29450702213127363790604165)
      ·
        refine ⟨5522006664961380710738281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29450702213127363790604165 5522006664961380710738281)
        ·
          refine ⟨4141504998721035533053711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5522006664961380710738281 4141504998721035533053711)
          ·
            refine ⟨6212257498081553299580567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141504998721035533053711 6212257498081553299580567)
            ·
              refine ⟨9318386247122329949370851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6212257498081553299580567 9318386247122329949370851)
              ·
                refine ⟨13977579370683494924056277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9318386247122329949370851 13977579370683494924056277)
                ·
                  refine ⟨327599516500394412282569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13977579370683494924056277 327599516500394412282569)
                  ·
                    rfl

theorem cell23_5741980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_5741980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741980 prefixEnd_5741980 := by exact prefixLift 5741980
  have htrace : WordTrace (prefixWord ++ tailWord_5741980) baseStart_5741980 baseEnd_5741980 := by
    simpa [prefixWord, tailWord_5741980, baseEnd_5741980] using wordTrace_append hprefix tailTrace_5741980
  have hstable : (prefixWord ++ tailWord_5741980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741980).length < 2 ^ (prefixWord ++ tailWord_5741980).sum := by decide
  have hdescent : baseEnd_5741980 < baseStart_5741980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741986 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5741986 : Nat := 118140960795 + 5741986 * 2 ^ 59
def prefixEnd_5741986 : Nat := 4983230072969 + 3 ^ 40 * 5741986 * 2
def baseEnd_5741986 : Nat := 2948398729387476687068093

theorem tailTrace_5741986 : CollatzResearch.WordTrace tailWord_5741986 prefixEnd_5741986 2948398729387476687068093 := by
  unfold tailWord_5741986
  simp only [CollatzResearch.WordTrace]
  refine ⟨52356858643943212495031453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139618289717181899986750541 52356858643943212495031453)
  ·
    refine ⟨19633821991478704685636795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52356858643943212495031453 19633821991478704685636795)
    ·
      refine ⟨29450732987218057028455193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19633821991478704685636795 29450732987218057028455193)
      ·
        refine ⟨22088049740413542771341395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29450732987218057028455193 22088049740413542771341395)
        ·
          refine ⟨33132074610620314157012093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22088049740413542771341395 33132074610620314157012093)
          ·
            refine ⟨12424527978982617808879535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33132074610620314157012093 12424527978982617808879535)
            ·
              refine ⟨18636791968473926713319303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12424527978982617808879535 18636791968473926713319303)
              ·
                refine ⟨27955187952710890069978955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18636791968473926713319303 27955187952710890069978955)
                ·
                  refine ⟨41932781929066335104968433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27955187952710890069978955 41932781929066335104968433)
                  ·
                    refine ⟨31449586446799751328726325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41932781929066335104968433 31449586446799751328726325)
                    ·
                      refine ⟨2948398729387476687068093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31449586446799751328726325 2948398729387476687068093)
                      ·
                        rfl

theorem cell23_5741986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5741986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741986 prefixEnd_5741986 := by exact prefixLift 5741986
  have htrace : WordTrace (prefixWord ++ tailWord_5741986) baseStart_5741986 baseEnd_5741986 := by
    simpa [prefixWord, tailWord_5741986, baseEnd_5741986] using wordTrace_append hprefix tailTrace_5741986
  have hstable : (prefixWord ++ tailWord_5741986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741986).length < 2 ^ (prefixWord ++ tailWord_5741986).sum := by decide
  have hdescent : baseEnd_5741986 < baseStart_5741986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741996 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 2, 4, 2]
def baseStart_5741996 : Nat := 118140960795 + 5741996 * 2 ^ 59
def prefixEnd_5741996 : Nat := 4983230072969 + 3 ^ 40 * 5741996 * 2
def baseEnd_5741996 : Nat := 2948403864194021647943047

theorem tailTrace_5741996 : CollatzResearch.WordTrace tailWord_5741996 prefixEnd_5741996 2948403864194021647943047 := by
  unfold tailWord_5741996
  simp only [CollatzResearch.WordTrace]
  refine ⟨104713899652868310843994921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139618532870491081125326561 104713899652868310843994921)
  ·
    refine ⟨78535424739651233132996191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104713899652868310843994921 78535424739651233132996191)
    ·
      refine ⟨117803137109476849699494287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78535424739651233132996191 117803137109476849699494287)
      ·
        refine ⟨176704705664215274549241431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117803137109476849699494287 176704705664215274549241431)
        ·
          refine ⟨265057058496322911823862147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176704705664215274549241431 265057058496322911823862147)
          ·
            refine ⟨397585587744484367735793221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265057058496322911823862147 397585587744484367735793221)
            ·
              refine ⟨74547297702090818950461229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 397585587744484367735793221 74547297702090818950461229)
              ·
                refine ⟨27955236638284057106422961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74547297702090818950461229 27955236638284057106422961)
                ·
                  refine ⟨20966427478713042829817221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27955236638284057106422961 20966427478713042829817221)
                  ·
                    refine ⟨3931205152258695530590729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20966427478713042829817221 3931205152258695530590729)
                    ·
                      refine ⟨2948403864194021647943047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3931205152258695530590729 2948403864194021647943047)
                      ·
                        rfl

theorem cell23_5741996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_5741996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741996 prefixEnd_5741996 := by exact prefixLift 5741996
  have htrace : WordTrace (prefixWord ++ tailWord_5741996) baseStart_5741996 baseEnd_5741996 := by
    simpa [prefixWord, tailWord_5741996, baseEnd_5741996] using wordTrace_append hprefix tailTrace_5741996
  have hstable : (prefixWord ++ tailWord_5741996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741996).length < 2 ^ (prefixWord ++ tailWord_5741996).sum := by decide
  have hdescent : baseEnd_5741996 < baseStart_5741996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5741999 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 3]
def baseStart_5741999 : Nat := 118140960795 + 5741999 * 2 ^ 59
def prefixEnd_5741999 : Nat := 4983230072969 + 3 ^ 40 * 5741999 * 2
def baseEnd_5741999 : Nat := 2948405404635985136205533

theorem tailTrace_5741999 : CollatzResearch.WordTrace tailWord_5741999 prefixEnd_5741999 2948405404635985136205533 := by
  unfold tailWord_5741999
  simp only [CollatzResearch.WordTrace]
  refine ⟨209427908724725753200349051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139618605816483835466899367 209427908724725753200349051)
  ·
    refine ⟨314141863087088629800523577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209427908724725753200349051 314141863087088629800523577)
    ·
      refine ⟨235606397315316472350392683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314141863087088629800523577 235606397315316472350392683)
      ·
        refine ⟨353409595972974708525589025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235606397315316472350392683 353409595972974708525589025)
        ·
          refine ⟨265057196979731031394191769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353409595972974708525589025 265057196979731031394191769)
          ·
            refine ⟨198792897734798273545643827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265057196979731031394191769 198792897734798273545643827)
            ·
              refine ⟨298189346602197410318465741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198792897734798273545643827 298189346602197410318465741)
              ·
                refine ⟨111821004975824028869424653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298189346602197410318465741 111821004975824028869424653)
                ·
                  refine ⟨41932876865934010826034245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111821004975824028869424653 41932876865934010826034245)
                  ·
                    refine ⟨7862414412362627029881421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41932876865934010826034245 7862414412362627029881421)
                    ·
                      refine ⟨2948405404635985136205533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7862414412362627029881421 2948405404635985136205533)
                      ·
                        rfl

theorem cell23_5741999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_5741999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5741999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5741999 prefixEnd_5741999 := by exact prefixLift 5741999
  have htrace : WordTrace (prefixWord ++ tailWord_5741999) baseStart_5741999 baseEnd_5741999 := by
    simpa [prefixWord, tailWord_5741999, baseEnd_5741999] using wordTrace_append hprefix tailTrace_5741999
  have hstable : (prefixWord ++ tailWord_5741999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5741999).length < 2 ^ (prefixWord ++ tailWord_5741999).sum := by decide
  have hdescent : baseEnd_5741999 < baseStart_5741999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5741999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
