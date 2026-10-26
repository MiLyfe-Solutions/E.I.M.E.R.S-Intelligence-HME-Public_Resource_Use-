import V185TrunkScan23Chunk0054

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_324624 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_324624 : Nat := 118140960795 + 324624 * 2 ^ 59
def prefixEnd_324624 : Nat := 4983230072969 + 3 ^ 40 * 324624 * 2
def baseEnd_324624 : Nat := 166688143985243140807087

theorem tailTrace_324624 : CollatzResearch.WordTrace tailWord_324624 prefixEnd_324624 166688143985243140807087 := by
  unfold tailWord_324624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5920004987975082105198463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7893339983966776140264617 5920004987975082105198463)
  ·
    refine ⟨8880007481962623157797695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5920004987975082105198463 8880007481962623157797695)
    ·
      refine ⟨13320011222943934736696543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8880007481962623157797695 13320011222943934736696543)
      ·
        refine ⟨19980016834415902105044815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13320011222943934736696543 19980016834415902105044815)
        ·
          refine ⟨29970025251623853157567223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19980016834415902105044815 29970025251623853157567223)
          ·
            refine ⟨44955037877435779736350835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29970025251623853157567223 44955037877435779736350835)
            ·
              refine ⟨67432556816153669604526253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44955037877435779736350835 67432556816153669604526253)
              ·
                refine ⟨25287208806057626101697345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67432556816153669604526253 25287208806057626101697345)
                ·
                  refine ⟨18965406604543219576273009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25287208806057626101697345 18965406604543219576273009)
                  ·
                    refine ⟨14224054953407414682204757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18965406604543219576273009 14224054953407414682204757)
                    ·
                      refine ⟨166688143985243140807087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 14224054953407414682204757 166688143985243140807087)
                      ·
                        rfl

theorem cell23_324624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_324624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324624 prefixEnd_324624 := by exact prefixLift 324624
  have htrace : WordTrace (prefixWord ++ tailWord_324624) baseStart_324624 baseEnd_324624 := by
    simpa [prefixWord, tailWord_324624, baseEnd_324624] using wordTrace_append hprefix tailTrace_324624
  have hstable : (prefixWord ++ tailWord_324624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324624).length < 2 ^ (prefixWord ++ tailWord_324624).sum := by decide
  have hdescent : baseEnd_324624 < baseStart_324624 := by decide
  rcases family_descends (prefixWord ++ tailWord_324624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324658 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_324658 : Nat := 118140960795 + 324658 * 2 ^ 59
def prefixEnd_324658 : Nat := 4983230072969 + 3 ^ 40 * 324658 * 2
def baseEnd_324658 : Nat := 166705602327496007781931

theorem tailTrace_324658 : CollatzResearch.WordTrace tailWord_324658 prefixEnd_324658 166705602327496007781931 := by
  unfold tailWord_324658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960312514456747004283657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7894166705217992011423085 2960312514456747004283657)
  ·
    refine ⟨2220234385842560253212743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2960312514456747004283657 2220234385842560253212743)
    ·
      refine ⟨3330351578763840379819115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220234385842560253212743 3330351578763840379819115)
      ·
        refine ⟨4995527368145760569728673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330351578763840379819115 4995527368145760569728673)
        ·
          refine ⟨3746645526109320427296505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4995527368145760569728673 3746645526109320427296505)
          ·
            refine ⟨2809984144581990320472379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3746645526109320427296505 2809984144581990320472379)
            ·
              refine ⟨4214976216872985480708569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809984144581990320472379 4214976216872985480708569)
              ·
                refine ⟨3161232162654739110531427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4214976216872985480708569 3161232162654739110531427)
                ·
                  refine ⟨4741848243982108665797141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161232162654739110531427 4741848243982108665797141)
                  ·
                    refine ⟨222274136436661343709241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4741848243982108665797141 222274136436661343709241)
                    ·
                      refine ⟨166705602327496007781931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 222274136436661343709241 166705602327496007781931)
                      ·
                        rfl

theorem cell23_324658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_324658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324658 prefixEnd_324658 := by exact prefixLift 324658
  have htrace : WordTrace (prefixWord ++ tailWord_324658) baseStart_324658 baseEnd_324658 := by
    simpa [prefixWord, tailWord_324658, baseEnd_324658] using wordTrace_append hprefix tailTrace_324658
  have hstable : (prefixWord ++ tailWord_324658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324658).length < 2 ^ (prefixWord ++ tailWord_324658).sum := by decide
  have hdescent : baseEnd_324658 < baseStart_324658 := by decide
  rcases family_descends (prefixWord ++ tailWord_324658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324681 : List Nat := [1, 2, 1, 1, 2, 2, 2, 6, 6]
def baseStart_324681 : Nat := 118140960795 + 324681 * 2 ^ 59
def prefixEnd_324681 : Nat := 4983230072969 + 3 ^ 40 * 324681 * 2
def baseEnd_324681 : Nat := 18524156931394379754925

theorem tailTrace_324681 : CollatzResearch.WordTrace tailWord_324681 prefixEnd_324681 18524156931394379754925 := by
  unfold tailWord_324681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842088936743662945221897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7894725957829108630147931 11842088936743662945221897)
  ·
    refine ⟨8881566702557747208916423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11842088936743662945221897 8881566702557747208916423)
    ·
      refine ⟨13322350053836620813374635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8881566702557747208916423 13322350053836620813374635)
      ·
        refine ⟨19983525080754931220061953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13322350053836620813374635 19983525080754931220061953)
        ·
          refine ⟨14987643810566198415046465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19983525080754931220061953 14987643810566198415046465)
          ·
            refine ⟨11240732857924648811284849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14987643810566198415046465 11240732857924648811284849)
            ·
              refine ⟨8430549643443486608463637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11240732857924648811284849 8430549643443486608463637)
              ·
                refine ⟨395182014536413434771733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8430549643443486608463637 395182014536413434771733)
                ·
                  refine ⟨18524156931394379754925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 395182014536413434771733 18524156931394379754925)
                  ·
                    rfl

theorem cell23_324681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 6, 6].length) (baseStart_324681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324681 prefixEnd_324681 := by exact prefixLift 324681
  have htrace : WordTrace (prefixWord ++ tailWord_324681) baseStart_324681 baseEnd_324681 := by
    simpa [prefixWord, tailWord_324681, baseEnd_324681] using wordTrace_append hprefix tailTrace_324681
  have hstable : (prefixWord ++ tailWord_324681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324681).length < 2 ^ (prefixWord ++ tailWord_324681).sum := by decide
  have hdescent : baseEnd_324681 < baseStart_324681 := by decide
  rcases family_descends (prefixWord ++ tailWord_324681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324685 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_324685 : Nat := 118140960795 + 324685 * 2 ^ 59
def prefixEnd_324685 : Nat := 4983230072969 + 3 ^ 40 * 324685 * 2
def baseEnd_324685 : Nat := 55573155435055800714769

theorem tailTrace_324685 : CollatzResearch.WordTrace tailWord_324685 prefixEnd_324685 55573155435055800714769 := by
  unfold tailWord_324685
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842234828729171628367509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7894823219152781085578339 11842234828729171628367509)
  ·
    refine ⟨555104757596679920079727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11842234828729171628367509 555104757596679920079727)
    ·
      refine ⟨832657136395019880119591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555104757596679920079727 832657136395019880119591)
      ·
        refine ⟨1248985704592529820179387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832657136395019880119591 1248985704592529820179387)
        ·
          refine ⟨1873478556888794730269081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248985704592529820179387 1873478556888794730269081)
          ·
            refine ⟨1405108917666596047701811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873478556888794730269081 1405108917666596047701811)
            ·
              refine ⟨2107663376499894071552717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405108917666596047701811 2107663376499894071552717)
              ·
                refine ⟨790373766187460276832269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2107663376499894071552717 790373766187460276832269)
                ·
                  refine ⟨296390162320297603812101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 790373766187460276832269 296390162320297603812101)
                  ·
                    refine ⟨55573155435055800714769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 296390162320297603812101 55573155435055800714769)
                    ·
                      rfl

theorem cell23_324685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_324685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324685 prefixEnd_324685 := by exact prefixLift 324685
  have htrace : WordTrace (prefixWord ++ tailWord_324685) baseStart_324685 baseEnd_324685 := by
    simpa [prefixWord, tailWord_324685, baseEnd_324685] using wordTrace_append hprefix tailTrace_324685
  have hstable : (prefixWord ++ tailWord_324685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324685).length < 2 ^ (prefixWord ++ tailWord_324685).sum := by decide
  have hdescent : baseEnd_324685 < baseStart_324685 := by decide
  rcases family_descends (prefixWord ++ tailWord_324685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324691 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 3]
def baseStart_324691 : Nat := 118140960795 + 324691 * 2 ^ 59
def prefixEnd_324691 : Nat := 4983230072969 + 3 ^ 40 * 324691 * 2
def baseEnd_324691 : Nat := 166722547189094378669279

theorem tailTrace_324691 : CollatzResearch.WordTrace tailWord_324691 prefixEnd_324691 166722547189094378669279 := by
  unfold tailWord_324691
  simp only [CollatzResearch.WordTrace]
  refine ⟨11842453666707434653085927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7894969111138289768723951 11842453666707434653085927)
  ·
    refine ⟨17763680500061151979628891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11842453666707434653085927 17763680500061151979628891)
    ·
      refine ⟨26645520750091727969443337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17763680500061151979628891 26645520750091727969443337)
      ·
        refine ⟨19984140562568795977082503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26645520750091727969443337 19984140562568795977082503)
        ·
          refine ⟨29976210843853193965623755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19984140562568795977082503 29976210843853193965623755)
          ·
            refine ⟨44964316265779790948435633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29976210843853193965623755 44964316265779790948435633)
            ·
              refine ⟨33723237199334843211326725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44964316265779790948435633 33723237199334843211326725)
              ·
                refine ⟨6323106974875283102123761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33723237199334843211326725 6323106974875283102123761)
                ·
                  refine ⟨4742330231156462326592821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6323106974875283102123761 4742330231156462326592821)
                  ·
                    refine ⟨444593459170918343118077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4742330231156462326592821 444593459170918343118077)
                    ·
                      refine ⟨166722547189094378669279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 444593459170918343118077 166722547189094378669279)
                      ·
                        rfl

theorem cell23_324691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_324691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324691 prefixEnd_324691 := by exact prefixLift 324691
  have htrace : WordTrace (prefixWord ++ tailWord_324691) baseStart_324691 baseEnd_324691 := by
    simpa [prefixWord, tailWord_324691, baseEnd_324691] using wordTrace_append hprefix tailTrace_324691
  have hstable : (prefixWord ++ tailWord_324691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324691).length < 2 ^ (prefixWord ++ tailWord_324691).sum := by decide
  have hdescent : baseEnd_324691 < baseStart_324691 := by decide
  rcases family_descends (prefixWord ++ tailWord_324691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324728 : List Nat := [2, 1, 2, 1, 1, 1, 6, 3, 1, 5]
def baseStart_324728 : Nat := 118140960795 + 324728 * 2 ^ 59
def prefixEnd_324728 : Nat := 4983230072969 + 3 ^ 40 * 324728 * 2
def baseEnd_324728 : Nat := 55580515324436911302203

theorem tailTrace_324728 : CollatzResearch.WordTrace tailWord_324728 prefixEnd_324728 55580515324436911302203 := by
  unfold tailWord_324728
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921901583786694986091419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7895868778382259981455225 5921901583786694986091419)
  ·
    refine ⟨8882852375680042479137129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5921901583786694986091419 8882852375680042479137129)
    ·
      refine ⟨6662139281760031859352847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8882852375680042479137129 6662139281760031859352847)
      ·
        refine ⟨9993208922640047789029271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6662139281760031859352847 9993208922640047789029271)
        ·
          refine ⟨14989813383960071683543907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9993208922640047789029271 14989813383960071683543907)
          ·
            refine ⟨22484720075940107525315861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14989813383960071683543907 22484720075940107525315861)
            ·
              refine ⟨1053971253559692540249181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22484720075940107525315861 1053971253559692540249181)
              ·
                refine ⟨395239220084884702593443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1053971253559692540249181 395239220084884702593443)
                ·
                  refine ⟨592858830127327053890165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395239220084884702593443 592858830127327053890165)
                  ·
                    refine ⟨55580515324436911302203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 592858830127327053890165 55580515324436911302203)
                    ·
                      rfl

theorem cell23_324728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_324728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324728 prefixEnd_324728 := by exact prefixLift 324728
  have htrace : WordTrace (prefixWord ++ tailWord_324728) baseStart_324728 baseEnd_324728 := by
    simpa [prefixWord, tailWord_324728, baseEnd_324728] using wordTrace_append hprefix tailTrace_324728
  have hstable : (prefixWord ++ tailWord_324728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324728).length < 2 ^ (prefixWord ++ tailWord_324728).sum := by decide
  have hdescent : baseEnd_324728 < baseStart_324728 := by decide
  rcases family_descends (prefixWord ++ tailWord_324728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324751 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 5]
def baseStart_324751 : Nat := 118140960795 + 324751 * 2 ^ 59
def prefixEnd_324751 : Nat := 4983230072969 + 3 ^ 40 * 324751 * 2
def baseEnd_324751 : Nat := 166753356028364143919003

theorem tailTrace_324751 : CollatzResearch.WordTrace tailWord_324751 prefixEnd_324751 166753356028364143919003 := by
  unfold tailWord_324751
  simp only [CollatzResearch.WordTrace]
  refine ⟨11844642046490064900270107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7896428030993376600180071 11844642046490064900270107)
  ·
    refine ⟨17766963069735097350405161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11844642046490064900270107 17766963069735097350405161)
    ·
      refine ⟨13325222302301323012803871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17766963069735097350405161 13325222302301323012803871)
      ·
        refine ⟨19987833453451984519205807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13325222302301323012803871 19987833453451984519205807)
        ·
          refine ⟨29981750180177976778808711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19987833453451984519205807 29981750180177976778808711)
          ·
            refine ⟨44972625270266965168213067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29981750180177976778808711 44972625270266965168213067)
            ·
              refine ⟨67458937905400447752319601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44972625270266965168213067 67458937905400447752319601)
              ·
                refine ⟨50594203429050335814239701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67458937905400447752319601 50594203429050335814239701)
                ·
                  refine ⟨1185801642868367245646243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 50594203429050335814239701 1185801642868367245646243)
                  ·
                    refine ⟨1778702464302550868469365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185801642868367245646243 1778702464302550868469365)
                    ·
                      refine ⟨166753356028364143919003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1778702464302550868469365 166753356028364143919003)
                      ·
                        rfl

theorem cell23_324751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_324751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324751 prefixEnd_324751 := by exact prefixLift 324751
  have htrace : WordTrace (prefixWord ++ tailWord_324751) baseStart_324751 baseEnd_324751 := by
    simpa [prefixWord, tailWord_324751, baseEnd_324751] using wordTrace_append hprefix tailTrace_324751
  have hstable : (prefixWord ++ tailWord_324751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324751).length < 2 ^ (prefixWord ++ tailWord_324751).sum := by decide
  have hdescent : baseEnd_324751 < baseStart_324751 := by decide
  rcases family_descends (prefixWord ++ tailWord_324751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324762 : List Nat := [3, 1, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_324762 : Nat := 118140960795 + 324762 * 2 ^ 59
def prefixEnd_324762 : Nat := 4983230072969 + 3 ^ 40 * 324762 * 2
def baseEnd_324762 : Nat := 55586334771854533627151

theorem tailTrace_324762 : CollatzResearch.WordTrace tailWord_324762 prefixEnd_324762 55586334771854533627151 := by
  unfold tailWord_324762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961260812362553444730135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7896695499633475852613693 2961260812362553444730135)
  ·
    refine ⟨4441891218543830167095203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2961260812362553444730135 4441891218543830167095203)
    ·
      refine ⟨6662836827815745250642805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4441891218543830167095203 6662836827815745250642805)
      ·
        refine ⟨624640952607726117247763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6662836827815745250642805 624640952607726117247763)
        ·
          refine ⟨936961428911589175871645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624640952607726117247763 936961428911589175871645)
          ·
            refine ⟨351360535841845940951867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 936961428911589175871645 351360535841845940951867)
            ·
              refine ⟨527040803762768911427801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351360535841845940951867 527040803762768911427801)
              ·
                refine ⟨395280602822076683570851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527040803762768911427801 395280602822076683570851)
                ·
                  refine ⟨592920904233115025356277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395280602822076683570851 592920904233115025356277)
                  ·
                    refine ⟨55586334771854533627151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 592920904233115025356277 55586334771854533627151)
                    ·
                      rfl

theorem cell23_324762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_324762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324762 prefixEnd_324762 := by exact prefixLift 324762
  have htrace : WordTrace (prefixWord ++ tailWord_324762) baseStart_324762 baseEnd_324762 := by
    simpa [prefixWord, tailWord_324762, baseEnd_324762] using wordTrace_append hprefix tailTrace_324762
  have hstable : (prefixWord ++ tailWord_324762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324762).length < 2 ^ (prefixWord ++ tailWord_324762).sum := by decide
  have hdescent : baseEnd_324762 < baseStart_324762 := by decide
  rcases family_descends (prefixWord ++ tailWord_324762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324775 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 1, 6]
def baseStart_324775 : Nat := 118140960795 + 324775 * 2 ^ 59
def prefixEnd_324775 : Nat := 4983230072969 + 3 ^ 40 * 324775 * 2
def baseEnd_324775 : Nat := 55588559854690683339631

theorem tailTrace_324775 : CollatzResearch.WordTrace tailWord_324775 prefixEnd_324775 55588559854690683339631 := by
  unfold tailWord_324775
  simp only [CollatzResearch.WordTrace]
  refine ⟨11845517398403116999143779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7897011598935411332762519 11845517398403116999143779)
  ·
    refine ⟨17768276097604675498715669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11845517398403116999143779 17768276097604675498715669)
    ·
      refine ⟨832887942075219164002297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17768276097604675498715669 832887942075219164002297)
      ·
        refine ⟨624665956556414373001723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 832887942075219164002297 624665956556414373001723)
        ·
          refine ⟨936998934834621559502585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624665956556414373001723 936998934834621559502585)
          ·
            refine ⟨702749201125966169626939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936998934834621559502585 702749201125966169626939)
            ·
              refine ⟨1054123801688949254440409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702749201125966169626939 1054123801688949254440409)
              ·
                refine ⟨790592851266711940830307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054123801688949254440409 790592851266711940830307)
                ·
                  refine ⟨1185889276900067911245461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790592851266711940830307 1185889276900067911245461)
                  ·
                    refine ⟨55588559854690683339631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1185889276900067911245461 55588559854690683339631)
                    ·
                      rfl

theorem cell23_324775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_324775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324775 prefixEnd_324775 := by exact prefixLift 324775
  have htrace : WordTrace (prefixWord ++ tailWord_324775) baseStart_324775 baseEnd_324775 := by
    simpa [prefixWord, tailWord_324775, baseEnd_324775] using wordTrace_append hprefix tailTrace_324775
  have hstable : (prefixWord ++ tailWord_324775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324775).length < 2 ^ (prefixWord ++ tailWord_324775).sum := by decide
  have hdescent : baseEnd_324775 < baseStart_324775 := by decide
  rcases family_descends (prefixWord ++ tailWord_324775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324785 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 5]
def baseStart_324785 : Nat := 118140960795 + 324785 * 2 ^ 59
def prefixEnd_324785 : Nat := 4983230072969 + 3 ^ 40 * 324785 * 2
def baseEnd_324785 : Nat := 166770814370617010893847

theorem tailTrace_324785 : CollatzResearch.WordTrace tailWord_324785 prefixEnd_324785 166770814370617010893847 := by
  unfold tailWord_324785
  simp only [CollatzResearch.WordTrace]
  refine ⟨11845882128366888707007809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7897254752244592471338539 11845882128366888707007809)
  ·
    refine ⟨8884411596275166530255857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11845882128366888707007809 8884411596275166530255857)
    ·
      refine ⟨6663308697206374897691893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8884411596275166530255857 6663308697206374897691893)
      ·
        refine ⟨624685190363097646658615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6663308697206374897691893 624685190363097646658615)
        ·
          refine ⟨937027785544646469987923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624685190363097646658615 937027785544646469987923)
          ·
            refine ⟨1405541678316969704981885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937027785544646469987923 1405541678316969704981885)
            ·
              refine ⟨527078129368863639368207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1405541678316969704981885 527078129368863639368207)
              ·
                refine ⟨790617194053295459052311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527078129368863639368207 790617194053295459052311)
                ·
                  refine ⟨1185925791079943188578467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790617194053295459052311 1185925791079943188578467)
                  ·
                    refine ⟨1778888686619914782867701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1185925791079943188578467 1778888686619914782867701)
                    ·
                      refine ⟨166770814370617010893847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1778888686619914782867701 166770814370617010893847)
                      ·
                        rfl

theorem cell23_324785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_324785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324785 prefixEnd_324785 := by exact prefixLift 324785
  have htrace : WordTrace (prefixWord ++ tailWord_324785) baseStart_324785 baseEnd_324785 := by
    simpa [prefixWord, tailWord_324785, baseEnd_324785] using wordTrace_append hprefix tailTrace_324785
  have hstable : (prefixWord ++ tailWord_324785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324785).length < 2 ^ (prefixWord ++ tailWord_324785).sum := by decide
  have hdescent : baseEnd_324785 < baseStart_324785 := by decide
  rcases family_descends (prefixWord ++ tailWord_324785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324818 : List Nat := [3, 2, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_324818 : Nat := 118140960795 + 324818 * 2 ^ 59
def prefixEnd_324818 : Nat := 4983230072969 + 3 ^ 40 * 324818 * 2
def baseEnd_324818 : Nat := 55595919744071793927065

theorem tailTrace_324818 : CollatzResearch.WordTrace tailWord_324818 prefixEnd_324818 55595919744071793927065 := by
  unfold tailWord_324818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961771434311833835739777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7898057158164890228639405 2961771434311833835739777)
  ·
    refine ⟨2221328575733875376804833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2961771434311833835739777 2221328575733875376804833)
    ·
      refine ⟨1665996431800406532603625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2221328575733875376804833 1665996431800406532603625)
      ·
        refine ⟨1249497323850304899452719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1665996431800406532603625 1249497323850304899452719)
        ·
          refine ⟨1874245985775457349179079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249497323850304899452719 1874245985775457349179079)
          ·
            refine ⟨2811368978663186023768619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874245985775457349179079 2811368978663186023768619)
            ·
              refine ⟨4217053467994779035652929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811368978663186023768619 4217053467994779035652929)
              ·
                refine ⟨3162790100996084276739697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217053467994779035652929 3162790100996084276739697)
                ·
                  refine ⟨2372092575747063207554773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162790100996084276739697 2372092575747063207554773)
                  ·
                    refine ⟨55595919744071793927065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2372092575747063207554773 55595919744071793927065)
                    ·
                      rfl

theorem cell23_324818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_324818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324818 prefixEnd_324818 := by exact prefixLift 324818
  have htrace : WordTrace (prefixWord ++ tailWord_324818) baseStart_324818 baseEnd_324818 := by
    simpa [prefixWord, tailWord_324818, baseEnd_324818] using wordTrace_append hprefix tailTrace_324818
  have hstable : (prefixWord ++ tailWord_324818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324818).length < 2 ^ (prefixWord ++ tailWord_324818).sum := by decide
  have hdescent : baseEnd_324818 < baseStart_324818 := by decide
  rcases family_descends (prefixWord ++ tailWord_324818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324866 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_324866 : Nat := 118140960795 + 324866 * 2 ^ 59
def prefixEnd_324866 : Nat := 4983230072969 + 3 ^ 40 * 324866 * 2
def baseEnd_324866 : Nat := 166812406303631193980975

theorem tailTrace_324866 : CollatzResearch.WordTrace tailWord_324866 prefixEnd_324866 166812406303631193980975 := by
  unfold tailWord_324866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962209110268359885176613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7899224294048959693804301 2962209110268359885176613)
  ·
    refine ⟨555414208175317478470615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2962209110268359885176613 555414208175317478470615)
    ·
      refine ⟨833121312262976217705923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555414208175317478470615 833121312262976217705923)
      ·
        refine ⟨1249681968394464326558885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833121312262976217705923 1249681968394464326558885)
        ·
          refine ⟨234315369073962061229791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1249681968394464326558885 234315369073962061229791)
          ·
            refine ⟨351473053610943091844687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234315369073962061229791 351473053610943091844687)
            ·
              refine ⟨527209580416414637767031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351473053610943091844687 527209580416414637767031)
              ·
                refine ⟨790814370624621956650547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527209580416414637767031 790814370624621956650547)
                ·
                  refine ⟨1186221555936932934975821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790814370624621956650547 1186221555936932934975821)
                  ·
                    refine ⟨444833083476349850615933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186221555936932934975821 444833083476349850615933)
                    ·
                      refine ⟨166812406303631193980975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 444833083476349850615933 166812406303631193980975)
                      ·
                        rfl

theorem cell23_324866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_324866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324866 prefixEnd_324866 := by exact prefixLift 324866
  have htrace : WordTrace (prefixWord ++ tailWord_324866) baseStart_324866 baseEnd_324866 := by
    simpa [prefixWord, tailWord_324866, baseEnd_324866] using wordTrace_append hprefix tailTrace_324866
  have hstable : (prefixWord ++ tailWord_324866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324866).length < 2 ^ (prefixWord ++ tailWord_324866).sum := by decide
  have hdescent : baseEnd_324866 < baseStart_324866 := by decide
  rcases family_descends (prefixWord ++ tailWord_324866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324912 : List Nat := [2, 1, 1, 1, 2, 2, 7, 2, 5]
def baseStart_324912 : Nat := 118140960795 + 324912 * 2 ^ 59
def prefixEnd_324912 : Nat := 4983230072969 + 3 ^ 40 * 324912 * 2
def baseEnd_324912 : Nat := 18537336268193112667307

theorem tailTrace_324912 : CollatzResearch.WordTrace tailWord_324912 prefixEnd_324912 18537336268193112667307 := by
  unfold tailWord_324912
  simp only [CollatzResearch.WordTrace]
  refine ⟨5925257099453394698440495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7900342799271192931253993 5925257099453394698440495)
  ·
    refine ⟨8887885649180092047660743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5925257099453394698440495 8887885649180092047660743)
    ·
      refine ⟨13331828473770138071491115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8887885649180092047660743 13331828473770138071491115)
      ·
        refine ⟨19997742710655207107236673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331828473770138071491115 19997742710655207107236673)
        ·
          refine ⟨14998307032991405330427505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19997742710655207107236673 14998307032991405330427505)
          ·
            refine ⟨11248730274743553997820629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14998307032991405330427505 11248730274743553997820629)
            ·
              refine ⟨263642115814302046823921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11248730274743553997820629 263642115814302046823921)
              ·
                refine ⟨197731586860726535117941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263642115814302046823921 197731586860726535117941)
                ·
                  refine ⟨18537336268193112667307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197731586860726535117941 18537336268193112667307)
                  ·
                    rfl

theorem cell23_324912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 2, 5].length) (baseStart_324912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324912 prefixEnd_324912 := by exact prefixLift 324912
  have htrace : WordTrace (prefixWord ++ tailWord_324912) baseStart_324912 baseEnd_324912 := by
    simpa [prefixWord, tailWord_324912, baseEnd_324912] using wordTrace_append hprefix tailTrace_324912
  have hstable : (prefixWord ++ tailWord_324912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324912).length < 2 ^ (prefixWord ++ tailWord_324912).sum := by decide
  have hdescent : baseEnd_324912 < baseStart_324912 := by decide
  rcases family_descends (prefixWord ++ tailWord_324912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324938 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_324938 : Nat := 118140960795 + 324938 * 2 ^ 59
def prefixEnd_324938 : Nat := 4983230072969 + 3 ^ 40 * 324938 * 2
def baseEnd_324938 : Nat := 55616458970251637426881

theorem tailTrace_324938 : CollatzResearch.WordTrace tailWord_324938 prefixEnd_324938 55616458970251637426881 := by
  unfold tailWord_324938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962865624203148959331867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7900974997875063891551645 2962865624203148959331867)
  ·
    refine ⟨4444298436304723438997801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2962865624203148959331867 4444298436304723438997801)
    ·
      refine ⟨3333223827228542579248351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4444298436304723438997801 3333223827228542579248351)
      ·
        refine ⟨4999835740842813868872527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3333223827228542579248351 4999835740842813868872527)
        ·
          refine ⟨7499753611264220803308791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4999835740842813868872527 7499753611264220803308791)
          ·
            refine ⟨11249630416896331204963187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499753611264220803308791 11249630416896331204963187)
            ·
              refine ⟨16874445625344496807444781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11249630416896331204963187 16874445625344496807444781)
              ·
                refine ⟨6327917109504186302791793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16874445625344496807444781 6327917109504186302791793)
                ·
                  refine ⟨4745937832128139727093845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6327917109504186302791793 4745937832128139727093845)
                  ·
                    refine ⟨55616458970251637426881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4745937832128139727093845 55616458970251637426881)
                    ·
                      rfl

theorem cell23_324938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_324938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324938 prefixEnd_324938 := by exact prefixLift 324938
  have htrace : WordTrace (prefixWord ++ tailWord_324938) baseStart_324938 baseEnd_324938 := by
    simpa [prefixWord, tailWord_324938, baseEnd_324938] using wordTrace_append hprefix tailTrace_324938
  have hstable : (prefixWord ++ tailWord_324938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324938).length < 2 ^ (prefixWord ++ tailWord_324938).sum := by decide
  have hdescent : baseEnd_324938 < baseStart_324938 := by decide
  rcases family_descends (prefixWord ++ tailWord_324938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324962 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_324962 : Nat := 118140960795 + 324962 * 2 ^ 59
def prefixEnd_324962 : Nat := 4983230072969 + 3 ^ 40 * 324962 * 2
def baseEnd_324962 : Nat := 166861700446462818380533

theorem tailTrace_324962 : CollatzResearch.WordTrace tailWord_324962 prefixEnd_324962 166861700446462818380533 := by
  unfold tailWord_324962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2963084462181411984050285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7901558565817098624134093 2963084462181411984050285)
  ·
    refine ⟨1111156673318029494018857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2963084462181411984050285 1111156673318029494018857)
    ·
      refine ⟨833367504988522120514143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1111156673318029494018857 833367504988522120514143)
      ·
        refine ⟨1250051257482783180771215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833367504988522120514143 1250051257482783180771215)
        ·
          refine ⟨1875076886224174771156823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250051257482783180771215 1875076886224174771156823)
          ·
            refine ⟨2812615329336262156735235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875076886224174771156823 2812615329336262156735235)
            ·
              refine ⟨4218922994004393235102853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812615329336262156735235 4218922994004393235102853)
              ·
                refine ⟨791048061375823731581785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4218922994004393235102853 791048061375823731581785)
                ·
                  refine ⟨593286046031867798686339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 791048061375823731581785 593286046031867798686339)
                  ·
                    refine ⟨889929069047801698029509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 593286046031867798686339 889929069047801698029509)
                    ·
                      refine ⟨166861700446462818380533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 889929069047801698029509 166861700446462818380533)
                      ·
                        rfl

theorem cell23_324962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_324962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324962 prefixEnd_324962 := by exact prefixLift 324962
  have htrace : WordTrace (prefixWord ++ tailWord_324962) baseStart_324962 baseEnd_324962 := by
    simpa [prefixWord, tailWord_324962, baseEnd_324962] using wordTrace_append hprefix tailTrace_324962
  have hstable : (prefixWord ++ tailWord_324962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324962).length < 2 ^ (prefixWord ++ tailWord_324962).sum := by decide
  have hdescent : baseEnd_324962 < baseStart_324962 := by decide
  rcases family_descends (prefixWord ++ tailWord_324962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324985 : List Nat := [1, 2, 1, 3, 2, 1, 4, 3, 6]
def baseStart_324985 : Nat := 118140960795 + 324985 * 2 ^ 59
def prefixEnd_324985 : Nat := 4983230072969 + 3 ^ 40 * 324985 * 2
def baseEnd_324985 : Nat := 18541501166835136488103

theorem tailTrace_324985 : CollatzResearch.WordTrace tailWord_324985 prefixEnd_324985 18541501166835136488103 := by
  unfold tailWord_324985
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853176727642322864288409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7902117818428215242858939 11853176727642322864288409)
  ·
    refine ⟨8889882545731742148216307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11853176727642322864288409 8889882545731742148216307)
    ·
      refine ⟨13334823818597613222324461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8889882545731742148216307 13334823818597613222324461)
      ·
        refine ⟨5000558931974104958371673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13334823818597613222324461 5000558931974104958371673)
        ·
          refine ⟨3750419198980578718778755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5000558931974104958371673 3750419198980578718778755)
          ·
            refine ⟨5625628798470868078168133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750419198980578718778755 5625628798470868078168133)
            ·
              refine ⟨1054805399713287764656525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5625628798470868078168133 1054805399713287764656525)
              ·
                refine ⟨395552024892482911746197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1054805399713287764656525 395552024892482911746197)
                ·
                  refine ⟨18541501166835136488103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 395552024892482911746197 18541501166835136488103)
                  ·
                    rfl

theorem cell23_324985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 6].length) (baseStart_324985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324985 prefixEnd_324985 := by exact prefixLift 324985
  have htrace : WordTrace (prefixWord ++ tailWord_324985) baseStart_324985 baseEnd_324985 := by
    simpa [prefixWord, tailWord_324985, baseEnd_324985] using wordTrace_append hprefix tailTrace_324985
  have hstable : (prefixWord ++ tailWord_324985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324985).length < 2 ^ (prefixWord ++ tailWord_324985).sum := by decide
  have hdescent : baseEnd_324985 < baseStart_324985 := by decide
  rcases family_descends (prefixWord ++ tailWord_324985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_324999 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_324999 : Nat := 118140960795 + 324999 * 2 ^ 59
def prefixEnd_324999 : Nat := 4983230072969 + 3 ^ 40 * 324999 * 2
def baseEnd_324999 : Nat := 166880699230679173617863

theorem tailTrace_324999 : CollatzResearch.WordTrace tailWord_324999 prefixEnd_324999 166880699230679173617863 := by
  unfold tailWord_324999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11853687349591603255298051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7902458233061068836865367 11853687349591603255298051)
  ·
    refine ⟨17780531024387404882947077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11853687349591603255298051 17780531024387404882947077)
    ·
      refine ⟨3333849567072638415552577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17780531024387404882947077 3333849567072638415552577)
      ·
        refine ⟨2500387175304478811664433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3333849567072638415552577 2500387175304478811664433)
        ·
          refine ⟨1875290381478359108748325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2500387175304478811664433 1875290381478359108748325)
          ·
            refine ⟨351616946527192332890311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1875290381478359108748325 351616946527192332890311)
            ·
              refine ⟨527425419790788499335467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351616946527192332890311 527425419790788499335467)
              ·
                refine ⟨791138129686182749003201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527425419790788499335467 791138129686182749003201)
                ·
                  refine ⟨593353597264637061752401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 791138129686182749003201 593353597264637061752401)
                  ·
                    refine ⟨445015197948477796314301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 593353597264637061752401 445015197948477796314301)
                    ·
                      refine ⟨166880699230679173617863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 445015197948477796314301 166880699230679173617863)
                      ·
                        rfl

theorem cell23_324999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_324999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_324999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_324999 prefixEnd_324999 := by exact prefixLift 324999
  have htrace : WordTrace (prefixWord ++ tailWord_324999) baseStart_324999 baseEnd_324999 := by
    simpa [prefixWord, tailWord_324999, baseEnd_324999] using wordTrace_append hprefix tailTrace_324999
  have hstable : (prefixWord ++ tailWord_324999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_324999).length < 2 ^ (prefixWord ++ tailWord_324999).sum := by decide
  have hdescent : baseEnd_324999 < baseStart_324999 := by decide
  rcases family_descends (prefixWord ++ tailWord_324999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325049 : List Nat := [1, 2, 1, 4, 4, 1, 2, 2, 1, 5]
def baseStart_325049 : Nat := 118140960795 + 325049 * 2 ^ 59
def prefixEnd_325049 : Nat := 4983230072969 + 3 ^ 40 * 325049 * 2
def baseEnd_325049 : Nat := 55635457754467992664211

theorem tailTrace_325049 : CollatzResearch.WordTrace tailWord_325049 prefixEnd_325049 55635457754467992664211 := by
  unfold tailWord_325049
  simp only [CollatzResearch.WordTrace]
  refine ⟨11855510999410461794618201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7903673999606974529745467 11855510999410461794618201)
  ·
    refine ⟨8891633249557846345963651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11855510999410461794618201 8891633249557846345963651)
    ·
      refine ⟨13337449874336769518945477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8891633249557846345963651 13337449874336769518945477)
      ·
        refine ⟨2500771851438144284802277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13337449874336769518945477 2500771851438144284802277)
        ·
          refine ⟨468894722144652053400427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2500771851438144284802277 468894722144652053400427)
          ·
            refine ⟨703342083216978080100641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468894722144652053400427 703342083216978080100641)
            ·
              refine ⟨527506562412733560075481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703342083216978080100641 527506562412733560075481)
              ·
                refine ⟨395629921809550170056611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527506562412733560075481 395629921809550170056611)
                ·
                  refine ⟨593444882714325255084917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395629921809550170056611 593444882714325255084917)
                  ·
                    refine ⟨55635457754467992664211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 593444882714325255084917 55635457754467992664211)
                    ·
                      rfl

theorem cell23_325049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_325049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325049 prefixEnd_325049 := by exact prefixLift 325049
  have htrace : WordTrace (prefixWord ++ tailWord_325049) baseStart_325049 baseEnd_325049 := by
    simpa [prefixWord, tailWord_325049, baseEnd_325049] using wordTrace_append hprefix tailTrace_325049
  have hstable : (prefixWord ++ tailWord_325049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325049).length < 2 ^ (prefixWord ++ tailWord_325049).sum := by decide
  have hdescent : baseEnd_325049 < baseStart_325049 := by decide
  rcases family_descends (prefixWord ++ tailWord_325049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325055 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 3]
def baseStart_325055 : Nat := 118140960795 + 325055 * 2 ^ 59
def prefixEnd_325055 : Nat := 4983230072969 + 3 ^ 40 * 325055 * 2
def baseEnd_325055 : Nat := 166909454147330954517605

theorem tailTrace_325055 : CollatzResearch.WordTrace tailWord_325055 prefixEnd_325055 166909454147330954517605 := by
  unfold tailWord_325055
  simp only [CollatzResearch.WordTrace]
  refine ⟨11855729837388724819336619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7903819891592483212891079 11855729837388724819336619)
  ·
    refine ⟨17783594756083087229004929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11855729837388724819336619 17783594756083087229004929)
    ·
      refine ⟨13337696067062315421753697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17783594756083087229004929 13337696067062315421753697)
      ·
        refine ⟨10003272050296736566315273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13337696067062315421753697 10003272050296736566315273)
        ·
          refine ⟨7502454037722552424736455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10003272050296736566315273 7502454037722552424736455)
          ·
            refine ⟨11253681056583828637104683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7502454037722552424736455 11253681056583828637104683)
            ·
              refine ⟨16880521584875742955657025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11253681056583828637104683 16880521584875742955657025)
              ·
                refine ⟨12660391188656807216742769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16880521584875742955657025 12660391188656807216742769)
                ·
                  refine ⟨9495293391492605412557077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12660391188656807216742769 9495293391492605412557077)
                  ·
                    refine ⟨445091877726215878713613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9495293391492605412557077 445091877726215878713613)
                    ·
                      refine ⟨166909454147330954517605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 445091877726215878713613 166909454147330954517605)
                      ·
                        rfl

theorem cell23_325055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_325055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325055 prefixEnd_325055 := by exact prefixLift 325055
  have htrace : WordTrace (prefixWord ++ tailWord_325055) baseStart_325055 baseEnd_325055 := by
    simpa [prefixWord, tailWord_325055, baseEnd_325055] using wordTrace_append hprefix tailTrace_325055
  have hstable : (prefixWord ++ tailWord_325055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325055).length < 2 ^ (prefixWord ++ tailWord_325055).sum := by decide
  have hdescent : baseEnd_325055 < baseStart_325055 := by decide
  rcases family_descends (prefixWord ++ tailWord_325055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325065 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 4]
def baseStart_325065 : Nat := 118140960795 + 325065 * 2 ^ 59
def prefixEnd_325065 : Nat := 4983230072969 + 3 ^ 40 * 325065 * 2
def baseEnd_325065 : Nat := 166914588953875915392559

theorem tailTrace_325065 : CollatzResearch.WordTrace tailWord_325065 prefixEnd_325065 166914588953875915392559 := by
  unfold tailWord_325065
  simp only [CollatzResearch.WordTrace]
  refine ⟨11856094567352496527200649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7904063044901664351467099 11856094567352496527200649)
  ·
    refine ⟨8892070925514372395400487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11856094567352496527200649 8892070925514372395400487)
    ·
      refine ⟨13338106388271558593100731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8892070925514372395400487 13338106388271558593100731)
      ·
        refine ⟨20007159582407337889651097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13338106388271558593100731 20007159582407337889651097)
        ·
          refine ⟨15005369686805503417238323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20007159582407337889651097 15005369686805503417238323)
          ·
            refine ⟨22508054530208255125857485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15005369686805503417238323 22508054530208255125857485)
            ·
              refine ⟨8440520448828095672196557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22508054530208255125857485 8440520448828095672196557)
              ·
                refine ⟨3165195168310535877073709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8440520448828095672196557 3165195168310535877073709)
                ·
                  refine ⟨1186948188116450953902641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3165195168310535877073709 1186948188116450953902641)
                  ·
                    refine ⟨890211141087338215426981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1186948188116450953902641 890211141087338215426981)
                    ·
                      refine ⟨166914588953875915392559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 890211141087338215426981 166914588953875915392559)
                      ·
                        rfl

theorem cell23_325065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_325065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325065 prefixEnd_325065 := by exact prefixLift 325065
  have htrace : WordTrace (prefixWord ++ tailWord_325065) baseStart_325065 baseEnd_325065 := by
    simpa [prefixWord, tailWord_325065, baseEnd_325065] using wordTrace_append hprefix tailTrace_325065
  have hstable : (prefixWord ++ tailWord_325065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325065).length < 2 ^ (prefixWord ++ tailWord_325065).sum := by decide
  have hdescent : baseEnd_325065 < baseStart_325065 := by decide
  rcases family_descends (prefixWord ++ tailWord_325065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325106 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_325106 : Nat := 118140960795 + 325106 * 2 ^ 59
def prefixEnd_325106 : Nat := 4983230072969 + 3 ^ 40 * 325106 * 2
def baseEnd_325106 : Nat := 166935641660710254979871

theorem tailTrace_325106 : CollatzResearch.WordTrace tailWord_325106 prefixEnd_325106 166935641660710254979871 := by
  unfold tailWord_325106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2964397490050990132360793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7905059973469307019628781 2964397490050990132360793)
  ·
    refine ⟨2223298117538242599270595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2964397490050990132360793 2223298117538242599270595)
    ·
      refine ⟨3334947176307363898905893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2223298117538242599270595 3334947176307363898905893)
      ·
        refine ⟨625302595557630731044855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3334947176307363898905893 625302595557630731044855)
        ·
          refine ⟨937953893336446096567283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625302595557630731044855 937953893336446096567283)
          ·
            refine ⟨1406930840004669144850925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937953893336446096567283 1406930840004669144850925)
            ·
              refine ⟨527599065001750929319097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1406930840004669144850925 527599065001750929319097)
              ·
                refine ⟨395699298751313196989323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527599065001750929319097 395699298751313196989323)
                ·
                  refine ⟨593548948126969795483985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395699298751313196989323 593548948126969795483985)
                  ·
                    refine ⟨445161711095227346612989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 593548948126969795483985 445161711095227346612989)
                    ·
                      refine ⟨166935641660710254979871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 445161711095227346612989 166935641660710254979871)
                      ·
                        rfl

theorem cell23_325106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_325106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325106 prefixEnd_325106 := by exact prefixLift 325106
  have htrace : WordTrace (prefixWord ++ tailWord_325106) baseStart_325106 baseEnd_325106 := by
    simpa [prefixWord, tailWord_325106, baseEnd_325106] using wordTrace_append hprefix tailTrace_325106
  have hstable : (prefixWord ++ tailWord_325106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325106).length < 2 ^ (prefixWord ++ tailWord_325106).sum := by decide
  have hdescent : baseEnd_325106 < baseStart_325106 := by decide
  rcases family_descends (prefixWord ++ tailWord_325106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325126 : List Nat := [6, 2, 1, 1, 2, 11]
def baseStart_325126 : Nat := 118140960795 + 325126 * 2 ^ 59
def prefixEnd_325126 : Nat := 4983230072969 + 3 ^ 40 * 325126 * 2
def baseEnd_325126 : Nat := 687020211003292908353

theorem tailTrace_325126 : CollatzResearch.WordTrace tailWord_325126 prefixEnd_325126 687020211003292908353 := by
  unfold tailWord_325126
  simp only [CollatzResearch.WordTrace]
  refine ⟨370572481879109498286601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7905546280087669296780821 370572481879109498286601)
  ·
    refine ⟨277929361409332123714951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 370572481879109498286601 277929361409332123714951)
    ·
      refine ⟨416894042113998185572427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277929361409332123714951 416894042113998185572427)
      ·
        refine ⟨625341063170997278358641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416894042113998185572427 625341063170997278358641)
        ·
          refine ⟨469005797378247958768981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625341063170997278358641 469005797378247958768981)
          ·
            refine ⟨687020211003292908353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 469005797378247958768981 687020211003292908353)
            ·
              rfl

theorem cell23_325126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 11].length) (baseStart_325126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325126 prefixEnd_325126 := by exact prefixLift 325126
  have htrace : WordTrace (prefixWord ++ tailWord_325126) baseStart_325126 baseEnd_325126 := by
    simpa [prefixWord, tailWord_325126, baseEnd_325126] using wordTrace_append hprefix tailTrace_325126
  have hstable : (prefixWord ++ tailWord_325126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325126).length < 2 ^ (prefixWord ++ tailWord_325126).sum := by decide
  have hdescent : baseEnd_325126 < baseStart_325126 := by decide
  rcases family_descends (prefixWord ++ tailWord_325126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325150 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_325150 : Nat := 118140960795 + 325150 * 2 ^ 59
def prefixEnd_325150 : Nat := 4983230072969 + 3 ^ 40 * 325150 * 2
def baseEnd_325150 : Nat := 166958234809508082829669

theorem tailTrace_325150 : CollatzResearch.WordTrace tailWord_325150 prefixEnd_325150 166958234809508082829669 := by
  unfold tailWord_325150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482399346505569505505613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7906129848029704029363269 1482399346505569505505613)
  ·
    refine ⟨555899754939588564564605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1482399346505569505505613 555899754939588564564605)
    ·
      refine ⟨208462408102345711711727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 555899754939588564564605 208462408102345711711727)
      ·
        refine ⟨312693612153518567567591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208462408102345711711727 312693612153518567567591)
        ·
          refine ⟨469040418230277851351387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312693612153518567567591 469040418230277851351387)
          ·
            refine ⟨703560627345416777027081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469040418230277851351387 703560627345416777027081)
            ·
              refine ⟨527670470509062582770311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 703560627345416777027081 527670470509062582770311)
              ·
                refine ⟨791505705763593874155467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527670470509062582770311 791505705763593874155467)
                ·
                  refine ⟨1187258558645390811233201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791505705763593874155467 1187258558645390811233201)
                  ·
                    refine ⟨890443918984043108424901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1187258558645390811233201 890443918984043108424901)
                    ·
                      refine ⟨166958234809508082829669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 890443918984043108424901 166958234809508082829669)
                      ·
                        rfl

theorem cell23_325150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_325150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325150 prefixEnd_325150 := by exact prefixLift 325150
  have htrace : WordTrace (prefixWord ++ tailWord_325150) baseStart_325150 baseEnd_325150 := by
    simpa [prefixWord, tailWord_325150, baseEnd_325150] using wordTrace_append hprefix tailTrace_325150
  have hstable : (prefixWord ++ tailWord_325150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325150).length < 2 ^ (prefixWord ++ tailWord_325150).sum := by decide
  have hdescent : baseEnd_325150 < baseStart_325150 := by decide
  rcases family_descends (prefixWord ++ tailWord_325150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325152 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 1, 8]
def baseStart_325152 : Nat := 118140960795 + 325152 * 2 ^ 59
def prefixEnd_325152 : Nat := 4983230072969 + 3 ^ 40 * 325152 * 2
def baseEnd_325152 : Nat := 55653087256939025001553

theorem tailTrace_325152 : CollatzResearch.WordTrace tailWord_325152 prefixEnd_325152 55653087256939025001553 := by
  unfold tailWord_325152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929633859018655192808855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7906178478691540257078473 5929633859018655192808855)
  ·
    refine ⟨8894450788527982789213283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5929633859018655192808855 8894450788527982789213283)
    ·
      refine ⟨13341676182791974183819925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8894450788527982789213283 13341676182791974183819925)
      ·
        refine ⟨625391071068373789866559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13341676182791974183819925 625391071068373789866559)
        ·
          refine ⟨938086606602560684799839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625391071068373789866559 938086606602560684799839)
          ·
            refine ⟨1407129909903841027199759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938086606602560684799839 1407129909903841027199759)
            ·
              refine ⟨2110694864855761540799639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407129909903841027199759 2110694864855761540799639)
              ·
                refine ⟨3166042297283642311199459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110694864855761540799639 3166042297283642311199459)
                ·
                  refine ⟨4749063445925463466799189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3166042297283642311199459 4749063445925463466799189)
                  ·
                    refine ⟨55653087256939025001553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4749063445925463466799189 55653087256939025001553)
                    ·
                      rfl

theorem cell23_325152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_325152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325152 prefixEnd_325152 := by exact prefixLift 325152
  have htrace : WordTrace (prefixWord ++ tailWord_325152) baseStart_325152 baseEnd_325152 := by
    simpa [prefixWord, tailWord_325152, baseEnd_325152] using wordTrace_append hprefix tailTrace_325152
  have hstable : (prefixWord ++ tailWord_325152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325152).length < 2 ^ (prefixWord ++ tailWord_325152).sum := by decide
  have hdescent : baseEnd_325152 < baseStart_325152 := by decide
  rcases family_descends (prefixWord ++ tailWord_325152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325180 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_325180 : Nat := 118140960795 + 325180 * 2 ^ 59
def prefixEnd_325180 : Nat := 4983230072969 + 3 ^ 40 * 325180 * 2
def baseEnd_325180 : Nat := 166973639229142965454531

theorem tailTrace_325180 : CollatzResearch.WordTrace tailWord_325180 prefixEnd_325180 166973639229142965454531 := by
  unfold tailWord_325180
  simp only [CollatzResearch.WordTrace]
  refine ⟨5930144480967935583818497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7906859307957247445091329 5930144480967935583818497)
  ·
    refine ⟨4447608360725951687863873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5930144480967935583818497 4447608360725951687863873)
    ·
      refine ⟨3335706270544463765897905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4447608360725951687863873 3335706270544463765897905)
      ·
        refine ⟨2501779702908347824423429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3335706270544463765897905 2501779702908347824423429)
        ·
          refine ⟨469083694295315217079393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2501779702908347824423429 469083694295315217079393)
          ·
            refine ⟨351812770721486412809545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469083694295315217079393 351812770721486412809545)
            ·
              refine ⟨263859578041114809607159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351812770721486412809545 263859578041114809607159)
              ·
                refine ⟨395789367061672214410739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263859578041114809607159 395789367061672214410739)
                ·
                  refine ⟨593684050592508321616109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 395789367061672214410739 593684050592508321616109)
                  ·
                    refine ⟨222631518972190620606041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 593684050592508321616109 222631518972190620606041)
                    ·
                      refine ⟨166973639229142965454531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 222631518972190620606041 166973639229142965454531)
                      ·
                        rfl

theorem cell23_325180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_325180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325180 prefixEnd_325180 := by exact prefixLift 325180
  have htrace : WordTrace (prefixWord ++ tailWord_325180) baseStart_325180 baseEnd_325180 := by
    simpa [prefixWord, tailWord_325180, baseEnd_325180] using wordTrace_append hprefix tailTrace_325180
  have hstable : (prefixWord ++ tailWord_325180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325180).length < 2 ^ (prefixWord ++ tailWord_325180).sum := by decide
  have hdescent : baseEnd_325180 < baseStart_325180 := by decide
  rcases family_descends (prefixWord ++ tailWord_325180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325249 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_325249 : Nat := 118140960795 + 325249 * 2 ^ 59
def prefixEnd_325249 : Nat := 4983230072969 + 3 ^ 40 * 325249 * 2
def baseEnd_325249 : Nat := 167009069394303195491713

theorem tailTrace_325249 : CollatzResearch.WordTrace tailWord_325249 prefixEnd_325249 167009069394303195491713 := by
  unfold tailWord_325249
  simp only [CollatzResearch.WordTrace]
  refine ⟨11862805598685895951898801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7908537065790597301265867 11862805598685895951898801)
  ·
    refine ⟨8897104199014421963924101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11862805598685895951898801 8897104199014421963924101)
    ·
      refine ⟨1668207037315204118235769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8897104199014421963924101 1668207037315204118235769)
      ·
        refine ⟨1251155277986403088676827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1668207037315204118235769 1251155277986403088676827)
        ·
          refine ⟨1876732916979604633015241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251155277986403088676827 1876732916979604633015241)
          ·
            refine ⟨1407549687734703474761431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876732916979604633015241 1407549687734703474761431)
            ·
              refine ⟨2111324531602055212142147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407549687734703474761431 2111324531602055212142147)
              ·
                refine ⟨3166986797403082818213221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111324531602055212142147 3166986797403082818213221)
                ·
                  refine ⟨593810024513078028414979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3166986797403082818213221 593810024513078028414979)
                  ·
                    refine ⟨890715036769617042622469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 593810024513078028414979 890715036769617042622469)
                    ·
                      refine ⟨167009069394303195491713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 890715036769617042622469 167009069394303195491713)
                      ·
                        rfl

theorem cell23_325249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_325249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325249 prefixEnd_325249 := by exact prefixLift 325249
  have htrace : WordTrace (prefixWord ++ tailWord_325249) baseStart_325249 baseEnd_325249 := by
    simpa [prefixWord, tailWord_325249, baseEnd_325249] using wordTrace_append hprefix tailTrace_325249
  have hstable : (prefixWord ++ tailWord_325249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325249).length < 2 ^ (prefixWord ++ tailWord_325249).sum := by decide
  have hdescent : baseEnd_325249 < baseStart_325249 := by decide
  rcases family_descends (prefixWord ++ tailWord_325249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325256 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_325256 : Nat := 118140960795 + 325256 * 2 ^ 59
def prefixEnd_325256 : Nat := 4983230072969 + 3 ^ 40 * 325256 * 2
def baseEnd_325256 : Nat := 167012663758884668104181

theorem tailTrace_325256 : CollatzResearch.WordTrace tailWord_325256 prefixEnd_325256 167012663758884668104181 := by
  unfold tailWord_325256
  simp only [CollatzResearch.WordTrace]
  refine ⟨5931530454830268073701811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7908707273107024098269081 5931530454830268073701811)
  ·
    refine ⟨8897295682245402110552717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5931530454830268073701811 8897295682245402110552717)
    ·
      refine ⟨3336485880842025791457269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8897295682245402110552717 3336485880842025791457269)
      ·
        refine ⟨312795551328939917949119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3336485880842025791457269 312795551328939917949119)
        ·
          refine ⟨469193326993409876923679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312795551328939917949119 469193326993409876923679)
          ·
            refine ⟨703789990490114815385519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469193326993409876923679 703789990490114815385519)
            ·
              refine ⟨1055684985735172223078279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703789990490114815385519 1055684985735172223078279)
              ·
                refine ⟨1583527478602758334617419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055684985735172223078279 1583527478602758334617419)
                ·
                  refine ⟨2375291217904137501926129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583527478602758334617419 2375291217904137501926129)
                  ·
                    refine ⟨1781468413428103126444597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2375291217904137501926129 1781468413428103126444597)
                    ·
                      refine ⟨167012663758884668104181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1781468413428103126444597 167012663758884668104181)
                      ·
                        rfl

theorem cell23_325256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_325256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325256 prefixEnd_325256 := by exact prefixLift 325256
  have htrace : WordTrace (prefixWord ++ tailWord_325256) baseStart_325256 baseEnd_325256 := by
    simpa [prefixWord, tailWord_325256, baseEnd_325256] using wordTrace_append hprefix tailTrace_325256
  have hstable : (prefixWord ++ tailWord_325256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325256).length < 2 ^ (prefixWord ++ tailWord_325256).sum := by decide
  have hdescent : baseEnd_325256 < baseStart_325256 := by decide
  rcases family_descends (prefixWord ++ tailWord_325256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325293 : List Nat := [1, 5, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_325293 : Nat := 118140960795 + 325293 * 2 ^ 59
def prefixEnd_325293 : Nat := 4983230072969 + 3 ^ 40 * 325293 * 2
def baseEnd_325293 : Nat := 55677220847700341113837

theorem tailTrace_325293 : CollatzResearch.WordTrace tailWord_325293 prefixEnd_325293 55677220847700341113837 := by
  unfold tailWord_325293
  simp only [CollatzResearch.WordTrace]
  refine ⟨11864410410526491466500533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7909606940350994311000355 11864410410526491466500533)
  ·
    refine ⟨1112288475986858574984425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11864410410526491466500533 1112288475986858574984425)
    ·
      refine ⟨834216356990143931238319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1112288475986858574984425 834216356990143931238319)
      ·
        refine ⟨1251324535485215896857479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834216356990143931238319 1251324535485215896857479)
        ·
          refine ⟨1876986803227823845286219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251324535485215896857479 1876986803227823845286219)
          ·
            refine ⟨2815480204841735767929329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876986803227823845286219 2815480204841735767929329)
            ·
              refine ⟨2111610153631301825946997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2815480204841735767929329 2111610153631301825946997)
              ·
                refine ⟨197963451902934546182531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2111610153631301825946997 197963451902934546182531)
                ·
                  refine ⟨296945177854401819273797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197963451902934546182531 296945177854401819273797)
                  ·
                    refine ⟨55677220847700341113837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 296945177854401819273797 55677220847700341113837)
                    ·
                      rfl

theorem cell23_325293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_325293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325293 prefixEnd_325293 := by exact prefixLift 325293
  have htrace : WordTrace (prefixWord ++ tailWord_325293) baseStart_325293 baseEnd_325293 := by
    simpa [prefixWord, tailWord_325293, baseEnd_325293] using wordTrace_append hprefix tailTrace_325293
  have hstable : (prefixWord ++ tailWord_325293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325293).length < 2 ^ (prefixWord ++ tailWord_325293).sum := by decide
  have hdescent : baseEnd_325293 < baseStart_325293 := by decide
  rcases family_descends (prefixWord ++ tailWord_325293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325310 : List Nat := [4, 2, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_325310 : Nat := 118140960795 + 325310 * 2 ^ 59
def prefixEnd_325310 : Nat := 4983230072969 + 3 ^ 40 * 325310 * 2
def baseEnd_325310 : Nat := 55680130571409152276311

theorem tailTrace_325310 : CollatzResearch.WordTrace tailWord_325310 prefixEnd_325310 55680130571409152276311 := by
  unfold tailWord_325310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483128806433112921233673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7910020300976602246579589 1483128806433112921233673)
  ·
    refine ⟨1112346604824834690925255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1483128806433112921233673 1112346604824834690925255)
    ·
      refine ⟨1668519907237252036387883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112346604824834690925255 1668519907237252036387883)
      ·
        refine ⟨2502779860855878054581825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668519907237252036387883 2502779860855878054581825)
        ·
          refine ⟨1877084895641908540936369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2502779860855878054581825 1877084895641908540936369)
          ·
            refine ⟨1407813671731431405702277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1877084895641908540936369 1407813671731431405702277)
            ·
              refine ⟨263965063449643388569177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1407813671731431405702277 263965063449643388569177)
              ·
                refine ⟨197973797587232541426883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263965063449643388569177 197973797587232541426883)
                ·
                  refine ⟨296960696380848812140325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197973797587232541426883 296960696380848812140325)
                  ·
                    refine ⟨55680130571409152276311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 296960696380848812140325 55680130571409152276311)
                    ·
                      rfl

theorem cell23_325310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_325310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325310 prefixEnd_325310 := by exact prefixLift 325310
  have htrace : WordTrace (prefixWord ++ tailWord_325310) baseStart_325310 baseEnd_325310 := by
    simpa [prefixWord, tailWord_325310, baseEnd_325310] using wordTrace_append hprefix tailTrace_325310
  have hstable : (prefixWord ++ tailWord_325310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325310).length < 2 ^ (prefixWord ++ tailWord_325310).sum := by decide
  have hdescent : baseEnd_325310 < baseStart_325310 := by decide
  rcases family_descends (prefixWord ++ tailWord_325310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325326 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_325326 : Nat := 118140960795 + 325326 * 2 ^ 59
def prefixEnd_325326 : Nat := 4983230072969 + 3 ^ 40 * 325326 * 2
def baseEnd_325326 : Nat := 167048607404699394228859

theorem tailTrace_325326 : CollatzResearch.WordTrace tailWord_325326 prefixEnd_325326 167048607404699394228859 := by
  unfold tailWord_325326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483201752425867262806479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7910409346271292068301221 1483201752425867262806479)
  ·
    refine ⟨2224802628638800894209719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1483201752425867262806479 2224802628638800894209719)
    ·
      refine ⟨3337203942958201341314579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224802628638800894209719 3337203942958201341314579)
      ·
        refine ⟨5005805914437302011971869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337203942958201341314579 5005805914437302011971869)
        ·
          refine ⟨1877177217913988254489451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5005805914437302011971869 1877177217913988254489451)
          ·
            refine ⟨2815765826870982381734177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877177217913988254489451 2815765826870982381734177)
            ·
              refine ⟨2111824370153236786300633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2815765826870982381734177 2111824370153236786300633)
              ·
                refine ⟨1583868277614927589725475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2111824370153236786300633 1583868277614927589725475)
                ·
                  refine ⟨2375802416422391384588213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583868277614927589725475 2375802416422391384588213)
                  ·
                    refine ⟨222731476539599192305145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2375802416422391384588213 222731476539599192305145)
                    ·
                      refine ⟨167048607404699394228859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 222731476539599192305145 167048607404699394228859)
                      ·
                        rfl

theorem cell23_325326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_325326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325326 prefixEnd_325326 := by exact prefixLift 325326
  have htrace : WordTrace (prefixWord ++ tailWord_325326) baseStart_325326 baseEnd_325326 := by
    simpa [prefixWord, tailWord_325326, baseEnd_325326] using wordTrace_append hprefix tailTrace_325326
  have hstable : (prefixWord ++ tailWord_325326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325326).length < 2 ^ (prefixWord ++ tailWord_325326).sum := by decide
  have hdescent : baseEnd_325326 < baseStart_325326 := by decide
  rcases family_descends (prefixWord ++ tailWord_325326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325349 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_325349 : Nat := 118140960795 + 325349 * 2 ^ 59
def prefixEnd_325349 : Nat := 4983230072969 + 3 ^ 40 * 325349 * 2
def baseEnd_325349 : Nat := 55686805819917601413751

theorem tailTrace_325349 : CollatzResearch.WordTrace tailWord_325349 prefixEnd_325349 55686805819917601413751 := by
  unfold tailWord_325349
  simp only [CollatzResearch.WordTrace]
  refine ⟨11866452898323613030539101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7910968598882408687026067 11866452898323613030539101)
  ·
    refine ⟨4449919836871354886452163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11866452898323613030539101 4449919836871354886452163)
    ·
      refine ⟨6674879755307032329678245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4449919836871354886452163 6674879755307032329678245)
      ·
        refine ⟨1251539954120068561814671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6674879755307032329678245 1251539954120068561814671)
        ·
          refine ⟨1877309931180102842722007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251539954120068561814671 1877309931180102842722007)
          ·
            refine ⟨2815964896770154264083011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877309931180102842722007 2815964896770154264083011)
            ·
              refine ⟨4223947345155231396124517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815964896770154264083011 4223947345155231396124517)
              ·
                refine ⟨791990127216605886773347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4223947345155231396124517 791990127216605886773347)
                ·
                  refine ⟨1187985190824908830160021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791990127216605886773347 1187985190824908830160021)
                  ·
                    refine ⟨55686805819917601413751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1187985190824908830160021 55686805819917601413751)
                    ·
                      rfl

theorem cell23_325349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_325349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325349 prefixEnd_325349 := by exact prefixLift 325349
  have htrace : WordTrace (prefixWord ++ tailWord_325349) baseStart_325349 baseEnd_325349 := by
    simpa [prefixWord, tailWord_325349, baseEnd_325349] using wordTrace_append hprefix tailTrace_325349
  have hstable : (prefixWord ++ tailWord_325349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325349).length < 2 ^ (prefixWord ++ tailWord_325349).sum := by decide
  have hdescent : baseEnd_325349 < baseStart_325349 := by decide
  rcases family_descends (prefixWord ++ tailWord_325349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325359 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 5]
def baseStart_325359 : Nat := 118140960795 + 325359 * 2 ^ 59
def prefixEnd_325359 : Nat := 4983230072969 + 3 ^ 40 * 325359 * 2
def baseEnd_325359 : Nat := 167065552266297765116207

theorem tailTrace_325359 : CollatzResearch.WordTrace tailWord_325359 prefixEnd_325359 167065552266297765116207 := by
  unfold tailWord_325359
  simp only [CollatzResearch.WordTrace]
  refine ⟨11866817628287384738403131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7911211752191589825602087 11866817628287384738403131)
  ·
    refine ⟨17800226442431077107604697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11866817628287384738403131 17800226442431077107604697)
    ·
      refine ⟨13350169831823307830703523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17800226442431077107604697 13350169831823307830703523)
      ·
        refine ⟨20025254747734961746055285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13350169831823307830703523 20025254747734961746055285)
        ·
          refine ⟨1877367632600152663692683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20025254747734961746055285 1877367632600152663692683)
          ·
            refine ⟨2816051448900228995539025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877367632600152663692683 2816051448900228995539025)
            ·
              refine ⟨2112038586675171746654269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2816051448900228995539025 2112038586675171746654269)
              ·
                refine ⟨792014470003189404995351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2112038586675171746654269 792014470003189404995351)
                ·
                  refine ⟨1188021705004784107493027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792014470003189404995351 1188021705004784107493027)
                  ·
                    refine ⟨1782032557507176161239541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1188021705004784107493027 1782032557507176161239541)
                    ·
                      refine ⟨167065552266297765116207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1782032557507176161239541 167065552266297765116207)
                      ·
                        rfl

theorem cell23_325359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_325359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325359 prefixEnd_325359 := by exact prefixLift 325359
  have htrace : WordTrace (prefixWord ++ tailWord_325359) baseStart_325359 baseEnd_325359 := by
    simpa [prefixWord, tailWord_325359, baseEnd_325359] using wordTrace_append hprefix tailTrace_325359
  have hstable : (prefixWord ++ tailWord_325359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325359).length < 2 ^ (prefixWord ++ tailWord_325359).sum := by decide
  have hdescent : baseEnd_325359 < baseStart_325359 := by decide
  rcases family_descends (prefixWord ++ tailWord_325359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325383 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 1, 6]
def baseStart_325383 : Nat := 118140960795 + 325383 * 2 ^ 59
def prefixEnd_325383 : Nat := 4983230072969 + 3 ^ 40 * 325383 * 2
def baseEnd_325383 : Nat := 55692625267335223738699

theorem tailTrace_325383 : CollatzResearch.WordTrace tailWord_325383 prefixEnd_325383 55692625267335223738699 := by
  unfold tailWord_325383
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867692980200436837276803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7911795320133624558184535 11867692980200436837276803)
  ·
    refine ⟨17801539470300655255915205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11867692980200436837276803 17801539470300655255915205)
    ·
      refine ⟨3337788650681372860484101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17801539470300655255915205 3337788650681372860484101)
      ·
        refine ⟨625835372002757411340769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3337788650681372860484101 625835372002757411340769)
        ·
          refine ⟨469376529002068058505577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625835372002757411340769 469376529002068058505577)
          ·
            refine ⟨352032396751551043879183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469376529002068058505577 352032396751551043879183)
            ·
              refine ⟨528048595127326565818775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352032396751551043879183 528048595127326565818775)
              ·
                refine ⟨792072892690989848728163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528048595127326565818775 792072892690989848728163)
                ·
                  refine ⟨1188109339036484773092245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792072892690989848728163 1188109339036484773092245)
                  ·
                    refine ⟨55692625267335223738699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1188109339036484773092245 55692625267335223738699)
                    ·
                      rfl

theorem cell23_325383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_325383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325383 prefixEnd_325383 := by exact prefixLift 325383
  have htrace : WordTrace (prefixWord ++ tailWord_325383) baseStart_325383 baseEnd_325383 := by
    simpa [prefixWord, tailWord_325383, baseEnd_325383] using wordTrace_append hprefix tailTrace_325383
  have hstable : (prefixWord ++ tailWord_325383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325383).length < 2 ^ (prefixWord ++ tailWord_325383).sum := by decide
  have hdescent : baseEnd_325383 < baseStart_325383 := by decide
  rcases family_descends (prefixWord ++ tailWord_325383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325386 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_325386 : Nat := 118140960795 + 325386 * 2 ^ 59
def prefixEnd_325386 : Nat := 4983230072969 + 3 ^ 40 * 325386 * 2
def baseEnd_325386 : Nat := 167079416243969159478583

theorem tailTrace_325386 : CollatzResearch.WordTrace tailWord_325386 prefixEnd_325386 167079416243969159478583 := by
  unfold tailWord_325386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966950599797392087409003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7911868266126378899757341 2966950599797392087409003)
  ·
    refine ⟨4450425899696088131113505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2966950599797392087409003 4450425899696088131113505)
    ·
      refine ⟨3337819424772066098335129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4450425899696088131113505 3337819424772066098335129)
      ·
        refine ⟨2503364568579049573751347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3337819424772066098335129 2503364568579049573751347)
        ·
          refine ⟨3755046852868574360627021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2503364568579049573751347 3755046852868574360627021)
          ·
            refine ⟨1408142569825715385235133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3755046852868574360627021 1408142569825715385235133)
            ·
              refine ⟨528053463684643269463175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1408142569825715385235133 528053463684643269463175)
              ·
                refine ⟨792080195526964904194763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528053463684643269463175 792080195526964904194763)
                ·
                  refine ⟨1188120293290447356292145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792080195526964904194763 1188120293290447356292145)
                  ·
                    refine ⟨891090219967835517219109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188120293290447356292145 891090219967835517219109)
                    ·
                      refine ⟨167079416243969159478583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 891090219967835517219109 167079416243969159478583)
                      ·
                        rfl

theorem cell23_325386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_325386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325386 prefixEnd_325386 := by exact prefixLift 325386
  have htrace : WordTrace (prefixWord ++ tailWord_325386) baseStart_325386 baseEnd_325386 := by
    simpa [prefixWord, tailWord_325386, baseEnd_325386] using wordTrace_append hprefix tailTrace_325386
  have hstable : (prefixWord ++ tailWord_325386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325386).length < 2 ^ (prefixWord ++ tailWord_325386).sum := by decide
  have hdescent : baseEnd_325386 < baseStart_325386 := by decide
  rcases family_descends (prefixWord ++ tailWord_325386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325449 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_325449 : Nat := 118140960795 + 325449 * 2 ^ 59
def prefixEnd_325449 : Nat := 4983230072969 + 3 ^ 40 * 325449 * 2
def baseEnd_325449 : Nat := 167111765525202412990793

theorem tailTrace_325449 : CollatzResearch.WordTrace tailWord_325449 prefixEnd_325449 167111765525202412990793 := by
  unfold tailWord_325449
  simp only [CollatzResearch.WordTrace]
  refine ⟨11870100197961330109179401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7913400131974220072786267 11870100197961330109179401)
  ·
    refine ⟨8902575148470997581884551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11870100197961330109179401 8902575148470997581884551)
    ·
      refine ⟨13353862722706496372826827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8902575148470997581884551 13353862722706496372826827)
      ·
        refine ⟨20030794084059744559240241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13353862722706496372826827 20030794084059744559240241)
        ·
          refine ⟨15023095563044808419430181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20030794084059744559240241 15023095563044808419430181)
          ·
            refine ⟨2816830418070901578643159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15023095563044808419430181 2816830418070901578643159)
            ·
              refine ⟨4225245627106352367964739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816830418070901578643159 4225245627106352367964739)
              ·
                refine ⟨6337868440659528551947109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225245627106352367964739 6337868440659528551947109)
                ·
                  refine ⟨1188350332623661603490083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6337868440659528551947109 1188350332623661603490083)
                  ·
                    refine ⟨1782525498935492405235125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1188350332623661603490083 1782525498935492405235125)
                    ·
                      refine ⟨167111765525202412990793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1782525498935492405235125 167111765525202412990793)
                      ·
                        rfl

theorem cell23_325449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_325449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325449 prefixEnd_325449 := by exact prefixLift 325449
  have htrace : WordTrace (prefixWord ++ tailWord_325449) baseStart_325449 baseEnd_325449 := by
    simpa [prefixWord, tailWord_325449, baseEnd_325449] using wordTrace_append hprefix tailTrace_325449
  have hstable : (prefixWord ++ tailWord_325449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325449).length < 2 ^ (prefixWord ++ tailWord_325449).sum := by decide
  have hdescent : baseEnd_325449 < baseStart_325449 := by decide
  rcases family_descends (prefixWord ++ tailWord_325449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325459 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4]
def baseStart_325459 : Nat := 118140960795 + 325459 * 2 ^ 59
def prefixEnd_325459 : Nat := 4983230072969 + 3 ^ 40 * 325459 * 2
def baseEnd_325459 : Nat := 167116900331747373865747

theorem tailTrace_325459 : CollatzResearch.WordTrace tailWord_325459 prefixEnd_325459 167116900331747373865747 := by
  unfold tailWord_325459
  simp only [CollatzResearch.WordTrace]
  refine ⟨11870464927925101817043431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7913643285283401211362287 11870464927925101817043431)
  ·
    refine ⟨17805697391887652725565147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11870464927925101817043431 17805697391887652725565147)
    ·
      refine ⟨26708546087831479088347721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17805697391887652725565147 26708546087831479088347721)
      ·
        refine ⟨20031409565873609316260791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26708546087831479088347721 20031409565873609316260791)
        ·
          refine ⟨30047114348810413974391187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20031409565873609316260791 30047114348810413974391187)
          ·
            refine ⟨45070671523215620961586781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30047114348810413974391187 45070671523215620961586781)
            ·
              refine ⟨16901501821205857860595043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45070671523215620961586781 16901501821205857860595043)
              ·
                refine ⟨25352252731808786790892565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16901501821205857860595043 25352252731808786790892565)
                ·
                  refine ⟨1188386846803536880823089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25352252731808786790892565 1188386846803536880823089)
                  ·
                    refine ⟨891290135102652660617317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1188386846803536880823089 891290135102652660617317)
                    ·
                      refine ⟨167116900331747373865747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 891290135102652660617317 167116900331747373865747)
                      ·
                        rfl

theorem cell23_325459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_325459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325459 prefixEnd_325459 := by exact prefixLift 325459
  have htrace : WordTrace (prefixWord ++ tailWord_325459) baseStart_325459 baseEnd_325459 := by
    simpa [prefixWord, tailWord_325459, baseEnd_325459] using wordTrace_append hprefix tailTrace_325459
  have hstable : (prefixWord ++ tailWord_325459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325459).length < 2 ^ (prefixWord ++ tailWord_325459).sum := by decide
  have hdescent : baseEnd_325459 < baseStart_325459 := by decide
  rcases family_descends (prefixWord ++ tailWord_325459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325499 : List Nat := [1, 1, 1, 1, 1, 5, 1, 4, 1, 7]
def baseStart_325499 : Nat := 118140960795 + 325499 * 2 ^ 59
def prefixEnd_325499 : Nat := 4983230072969 + 3 ^ 40 * 325499 * 2
def baseEnd_325499 : Nat := 55712479852642405788521

theorem tailTrace_325499 : CollatzResearch.WordTrace tailWord_325499 prefixEnd_325499 55712479852642405788521 := by
  unfold tailWord_325499
  simp only [CollatzResearch.WordTrace]
  refine ⟨11871923847780188648499551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7914615898520125765666367 11871923847780188648499551)
  ·
    refine ⟨17807885771670282972749327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11871923847780188648499551 17807885771670282972749327)
    ·
      refine ⟨26711828657505424459123991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17807885771670282972749327 26711828657505424459123991)
      ·
        refine ⟨40067742986258136688685987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26711828657505424459123991 40067742986258136688685987)
        ·
          refine ⟨60101614479387205033028981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40067742986258136688685987 60101614479387205033028981)
          ·
            refine ⟨5634526357442550471846467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60101614479387205033028981 5634526357442550471846467)
            ·
              refine ⟨8451789536163825707769701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634526357442550471846467 8451789536163825707769701)
              ·
                refine ⟨1584710538030717320206819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8451789536163825707769701 1584710538030717320206819)
                ·
                  refine ⟨2377065807046075980310229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584710538030717320206819 2377065807046075980310229)
                  ·
                    refine ⟨55712479852642405788521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2377065807046075980310229 55712479852642405788521)
                    ·
                      rfl

theorem cell23_325499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 7].length) (baseStart_325499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325499 prefixEnd_325499 := by exact prefixLift 325499
  have htrace : WordTrace (prefixWord ++ tailWord_325499) baseStart_325499 baseEnd_325499 := by
    simpa [prefixWord, tailWord_325499, baseEnd_325499] using wordTrace_append hprefix tailTrace_325499
  have hstable : (prefixWord ++ tailWord_325499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325499).length < 2 ^ (prefixWord ++ tailWord_325499).sum := by decide
  have hdescent : baseEnd_325499 < baseStart_325499 := by decide
  rcases family_descends (prefixWord ++ tailWord_325499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325536 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_325536 : Nat := 118140960795 + 325536 * 2 ^ 59
def prefixEnd_325536 : Nat := 4983230072969 + 3 ^ 40 * 325536 * 2
def baseEnd_325536 : Nat := 167156438342143572602893

theorem tailTrace_325536 : CollatzResearch.WordTrace tailWord_325536 prefixEnd_325536 167156438342143572602893 := by
  unfold tailWord_325536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936636674323071983798231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7915515565764095978397641 5936636674323071983798231)
  ·
    refine ⟨8904955011484607975697347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5936636674323071983798231 8904955011484607975697347)
    ·
      refine ⟨13357432517226911963546021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8904955011484607975697347 13357432517226911963546021)
      ·
        refine ⟨2504518596980045993164879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13357432517226911963546021 2504518596980045993164879)
        ·
          refine ⟨3756777895470068989747319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504518596980045993164879 3756777895470068989747319)
          ·
            refine ⟨5635166843205103484620979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756777895470068989747319 5635166843205103484620979)
            ·
              refine ⟨8452750264807655226931469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5635166843205103484620979 8452750264807655226931469)
              ·
                refine ⟨3169781349302870710099301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8452750264807655226931469 3169781349302870710099301)
                ·
                  refine ⟨594334002994288258143619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3169781349302870710099301 594334002994288258143619)
                  ·
                    refine ⟨891501004491432387215429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 594334002994288258143619 891501004491432387215429)
                    ·
                      refine ⟨167156438342143572602893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 891501004491432387215429 167156438342143572602893)
                      ·
                        rfl

theorem cell23_325536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_325536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325536 prefixEnd_325536 := by exact prefixLift 325536
  have htrace : WordTrace (prefixWord ++ tailWord_325536) baseStart_325536 baseEnd_325536 := by
    simpa [prefixWord, tailWord_325536, baseEnd_325536] using wordTrace_append hprefix tailTrace_325536
  have hstable : (prefixWord ++ tailWord_325536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325536).length < 2 ^ (prefixWord ++ tailWord_325536).sum := by decide
  have hdescent : baseEnd_325536 < baseStart_325536 := by decide
  rcases family_descends (prefixWord ++ tailWord_325536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325576 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 8]
def baseStart_325576 : Nat := 118140960795 + 325576 * 2 ^ 59
def prefixEnd_325576 : Nat := 4983230072969 + 3 ^ 40 * 325576 * 2
def baseEnd_325576 : Nat := 18575219729813712900301

theorem tailTrace_325576 : CollatzResearch.WordTrace tailWord_325576 prefixEnd_325576 18575219729813712900301 := by
  unfold tailWord_325576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937366134250615399526291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7916488179000820532701721 5937366134250615399526291)
  ·
    refine ⟨8906049201375923099289437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5937366134250615399526291 8906049201375923099289437)
    ·
      refine ⟨3339768450515971162233539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8906049201375923099289437 3339768450515971162233539)
      ·
        refine ⟨5009652675773956743350309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339768450515971162233539 5009652675773956743350309)
        ·
          refine ⟨939309876707616889378183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5009652675773956743350309 939309876707616889378183)
          ·
            refine ⟨1408964815061425334067275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939309876707616889378183 1408964815061425334067275)
            ·
              refine ⟨2113447222592138001100913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408964815061425334067275 2113447222592138001100913)
              ·
                refine ⟨1585085416944103500825685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113447222592138001100913 1585085416944103500825685)
                ·
                  refine ⟨18575219729813712900301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1585085416944103500825685 18575219729813712900301)
                  ·
                    rfl

theorem cell23_325576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 8].length) (baseStart_325576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325576 prefixEnd_325576 := by exact prefixLift 325576
  have htrace : WordTrace (prefixWord ++ tailWord_325576) baseStart_325576 baseEnd_325576 := by
    simpa [prefixWord, tailWord_325576, baseEnd_325576] using wordTrace_append hprefix tailTrace_325576
  have hstable : (prefixWord ++ tailWord_325576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325576).length < 2 ^ (prefixWord ++ tailWord_325576).sum := by decide
  have hdescent : baseEnd_325576 < baseStart_325576 := by decide
  rcases family_descends (prefixWord ++ tailWord_325576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325597 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_325597 : Nat := 118140960795 + 325597 * 2 ^ 59
def prefixEnd_325597 : Nat := 4983230072969 + 3 ^ 40 * 325597 * 2
def baseEnd_325597 : Nat := 55729253554022611313371

theorem tailTrace_325597 : CollatzResearch.WordTrace tailWord_325597 prefixEnd_325597 55729253554022611313371 := by
  unfold tailWord_325597
  simp only [CollatzResearch.WordTrace]
  refine ⟨11875498201425151385567045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7916998800950100923711363 11875498201425151385567045)
  ·
    refine ⟨2226655912767215884793821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11875498201425151385567045 2226655912767215884793821)
    ·
      refine ⟨834995967287705956797683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2226655912767215884793821 834995967287705956797683)
      ·
        refine ⟨1252493950931558935196525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834995967287705956797683 1252493950931558935196525)
        ·
          refine ⟨469685231599334600698697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1252493950931558935196525 469685231599334600698697)
          ·
            refine ⟨352263923699500950524023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469685231599334600698697 352263923699500950524023)
            ·
              refine ⟨528395885549251425786035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352263923699500950524023 528395885549251425786035)
              ·
                refine ⟨792593828323877138679053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528395885549251425786035 792593828323877138679053)
                ·
                  refine ⟨297222685621453927004645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 792593828323877138679053 297222685621453927004645)
                  ·
                    refine ⟨55729253554022611313371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297222685621453927004645 55729253554022611313371)
                    ·
                      rfl

theorem cell23_325597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_325597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325597 prefixEnd_325597 := by exact prefixLift 325597
  have htrace : WordTrace (prefixWord ++ tailWord_325597) baseStart_325597 baseEnd_325597 := by
    simpa [prefixWord, tailWord_325597, baseEnd_325597] using wordTrace_append hprefix tailTrace_325597
  have hstable : (prefixWord ++ tailWord_325597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325597).length < 2 ^ (prefixWord ++ tailWord_325597).sum := by decide
  have hdescent : baseEnd_325597 < baseStart_325597 := by decide
  rcases family_descends (prefixWord ++ tailWord_325597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325640 : List Nat := [2, 1, 3, 2, 1, 2, 5, 1, 1, 5]
def baseStart_325640 : Nat := 118140960795 + 325640 * 2 ^ 59
def prefixEnd_325640 : Nat := 4983230072969 + 3 ^ 40 * 325640 * 2
def baseEnd_325640 : Nat := 55736613443403721900805

theorem tailTrace_325640 : CollatzResearch.WordTrace tailWord_325640 prefixEnd_325640 55736613443403721900805 := by
  unfold tailWord_325640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5938533270134684864691187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7918044360179579819588249 5938533270134684864691187)
  ·
    refine ⟨8907799905202027297036781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5938533270134684864691187 8907799905202027297036781)
    ·
      refine ⟨3340424964450760236388793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8907799905202027297036781 3340424964450760236388793)
      ·
        refine ⟨2505318723338070177291595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3340424964450760236388793 2505318723338070177291595)
        ·
          refine ⟨3757978085007105265937393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505318723338070177291595 3757978085007105265937393)
          ·
            refine ⟨2818483563755328949453045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3757978085007105265937393 2818483563755328949453045)
            ·
              refine ⟨264232834102062089011223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2818483563755328949453045 264232834102062089011223)
              ·
                refine ⟨396349251153093133516835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264232834102062089011223 396349251153093133516835)
                ·
                  refine ⟨594523876729639700275253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396349251153093133516835 594523876729639700275253)
                  ·
                    refine ⟨55736613443403721900805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 594523876729639700275253 55736613443403721900805)
                    ·
                      rfl

theorem cell23_325640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_325640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325640 prefixEnd_325640 := by exact prefixLift 325640
  have htrace : WordTrace (prefixWord ++ tailWord_325640) baseStart_325640 baseEnd_325640 := by
    simpa [prefixWord, tailWord_325640, baseEnd_325640] using wordTrace_append hprefix tailTrace_325640
  have hstable : (prefixWord ++ tailWord_325640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325640).length < 2 ^ (prefixWord ++ tailWord_325640).sum := by decide
  have hdescent : baseEnd_325640 < baseStart_325640 := by decide
  rcases family_descends (prefixWord ++ tailWord_325640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325663 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 3]
def baseStart_325663 : Nat := 118140960795 + 325663 * 2 ^ 59
def prefixEnd_325663 : Nat := 4983230072969 + 3 ^ 40 * 325663 * 2
def baseEnd_325663 : Nat := 167221650385264575714809

theorem tailTrace_325663 : CollatzResearch.WordTrace tailWord_325663 prefixEnd_325663 167221650385264575714809 := by
  unfold tailWord_325663
  simp only [CollatzResearch.WordTrace]
  refine ⟨11877905419186044657469643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7918603612790696438313095 11877905419186044657469643)
  ·
    refine ⟨17816858128779066986204465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11877905419186044657469643 17816858128779066986204465)
    ·
      refine ⟨13362643596584300239653349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17816858128779066986204465 13362643596584300239653349)
      ·
        refine ⟨2505495674359556294935003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13362643596584300239653349 2505495674359556294935003)
        ·
          refine ⟨3758243511539334442402505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505495674359556294935003 3758243511539334442402505)
          ·
            refine ⟨2818682633654500831801879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3758243511539334442402505 2818682633654500831801879)
            ·
              refine ⟨4228023950481751247702819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818682633654500831801879 4228023950481751247702819)
              ·
                refine ⟨6342035925722626871554229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228023950481751247702819 6342035925722626871554229)
                ·
                  refine ⟨594565868036496269208209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6342035925722626871554229 594565868036496269208209)
                  ·
                    refine ⟨445924401027372201906157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 594565868036496269208209 445924401027372201906157)
                    ·
                      refine ⟨167221650385264575714809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 445924401027372201906157 167221650385264575714809)
                      ·
                        rfl

theorem cell23_325663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_325663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325663 prefixEnd_325663 := by exact prefixLift 325663
  have htrace : WordTrace (prefixWord ++ tailWord_325663) baseStart_325663 baseEnd_325663 := by
    simpa [prefixWord, tailWord_325663, baseEnd_325663] using wordTrace_append hprefix tailTrace_325663
  have hstable : (prefixWord ++ tailWord_325663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325663).length < 2 ^ (prefixWord ++ tailWord_325663).sum := by decide
  have hdescent : baseEnd_325663 < baseStart_325663 := by decide
  rcases family_descends (prefixWord ++ tailWord_325663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325697 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_325697 : Nat := 118140960795 + 325697 * 2 ^ 59
def prefixEnd_325697 : Nat := 4983230072969 + 3 ^ 40 * 325697 * 2
def baseEnd_325697 : Nat := 167239108727517442689653

theorem tailTrace_325697 : CollatzResearch.WordTrace tailWord_325697 prefixEnd_325697 167239108727517442689653 := by
  unfold tailWord_325697
  simp only [CollatzResearch.WordTrace]
  refine ⟨11879145501062868464207345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7919430334041912309471563 11879145501062868464207345)
  ·
    refine ⟨8909359125797151348155509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11879145501062868464207345 8909359125797151348155509)
    ·
      refine ⟨835252418043482938889579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8909359125797151348155509 835252418043482938889579)
      ·
        refine ⟨1252878627065224408334369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835252418043482938889579 1252878627065224408334369)
        ·
          refine ⟨939658970298918306250777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252878627065224408334369 939658970298918306250777)
          ·
            refine ⟨704744227724188729688083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939658970298918306250777 704744227724188729688083)
            ·
              refine ⟨1057116341586283094532125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704744227724188729688083 1057116341586283094532125)
              ·
                refine ⟨396418628094856160449547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057116341586283094532125 396418628094856160449547)
                ·
                  refine ⟨594627942142284240674321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396418628094856160449547 594627942142284240674321)
                  ·
                    refine ⟨445970956606713180505741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 594627942142284240674321 445970956606713180505741)
                    ·
                      refine ⟨167239108727517442689653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 445970956606713180505741 167239108727517442689653)
                      ·
                        rfl

theorem cell23_325697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_325697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325697 prefixEnd_325697 := by exact prefixLift 325697
  have htrace : WordTrace (prefixWord ++ tailWord_325697) baseStart_325697 baseEnd_325697 := by
    simpa [prefixWord, tailWord_325697, baseEnd_325697] using wordTrace_append hprefix tailTrace_325697
  have hstable : (prefixWord ++ tailWord_325697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325697).length < 2 ^ (prefixWord ++ tailWord_325697).sum := by decide
  have hdescent : baseEnd_325697 < baseStart_325697 := by decide
  rcases family_descends (prefixWord ++ tailWord_325697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325737 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 1, 3, 2]
def baseStart_325737 : Nat := 118140960795 + 325737 * 2 ^ 59
def prefixEnd_325737 : Nat := 4983230072969 + 3 ^ 40 * 325737 * 2
def baseEnd_325737 : Nat := 167259647953697286189469

theorem tailTrace_325737 : CollatzResearch.WordTrace tailWord_325737 prefixEnd_325737 167259647953697286189469 := by
  unfold tailWord_325737
  simp only [CollatzResearch.WordTrace]
  refine ⟨11880604420917955295663465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7920402947278636863775643 11880604420917955295663465)
  ·
    refine ⟨8910453315688466471747599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11880604420917955295663465 8910453315688466471747599)
    ·
      refine ⟨13365679973532699707621399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8910453315688466471747599 13365679973532699707621399)
      ·
        refine ⟨20048519960299049561432099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13365679973532699707621399 20048519960299049561432099)
        ·
          refine ⟨30072779940448574342148149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20048519960299049561432099 30072779940448574342148149)
          ·
            refine ⟨2819323119417053844576389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30072779940448574342148149 2819323119417053844576389)
            ·
              refine ⟨528623084890697595858073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2819323119417053844576389 528623084890697595858073)
              ·
                refine ⟨396467313668023196893555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528623084890697595858073 396467313668023196893555)
                ·
                  refine ⟨594700970502034795340333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396467313668023196893555 594700970502034795340333)
                  ·
                    refine ⟨223012863938263048252625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 594700970502034795340333 223012863938263048252625)
                    ·
                      refine ⟨167259647953697286189469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223012863938263048252625 167259647953697286189469)
                      ·
                        rfl

theorem cell23_325737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 3, 2].length) (baseStart_325737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325737 prefixEnd_325737 := by exact prefixLift 325737
  have htrace : WordTrace (prefixWord ++ tailWord_325737) baseStart_325737 baseEnd_325737 := by
    simpa [prefixWord, tailWord_325737, baseEnd_325737] using wordTrace_append hprefix tailTrace_325737
  have hstable : (prefixWord ++ tailWord_325737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325737).length < 2 ^ (prefixWord ++ tailWord_325737).sum := by decide
  have hdescent : baseEnd_325737 < baseStart_325737 := by decide
  rcases family_descends (prefixWord ++ tailWord_325737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325753 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_325753 : Nat := 118140960795 + 325753 * 2 ^ 59
def prefixEnd_325753 : Nat := 4983230072969 + 3 ^ 40 * 325753 * 2
def baseEnd_325753 : Nat := 167267863644169223589395

theorem tailTrace_325753 : CollatzResearch.WordTrace tailWord_325753 prefixEnd_325753 167267863644169223589395 := by
  unfold tailWord_325753
  simp only [CollatzResearch.WordTrace]
  refine ⟨11881187988859990028245913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7920791992573326685497275 11881187988859990028245913)
  ·
    refine ⟨8910890991644992521184435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11881187988859990028245913 8910890991644992521184435)
    ·
      refine ⟨13366336487467488781776653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8910890991644992521184435 13366336487467488781776653)
      ·
        refine ⟨5012376182800308293166245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13366336487467488781776653 5012376182800308293166245)
        ·
          refine ⟨939820534275057804968671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5012376182800308293166245 939820534275057804968671)
          ·
            refine ⟨1409730801412586707453007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939820534275057804968671 1409730801412586707453007)
            ·
              refine ⟨2114596202118880061179511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409730801412586707453007 2114596202118880061179511)
              ·
                refine ⟨3171894303178320091769267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114596202118880061179511 3171894303178320091769267)
                ·
                  refine ⟨4757841454767480137653901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171894303178320091769267 4757841454767480137653901)
                  ·
                    refine ⟨1784190545537805051620213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4757841454767480137653901 1784190545537805051620213)
                    ·
                      refine ⟨167267863644169223589395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1784190545537805051620213 167267863644169223589395)
                      ·
                        rfl

theorem cell23_325753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_325753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325753 prefixEnd_325753 := by exact prefixLift 325753
  have htrace : WordTrace (prefixWord ++ tailWord_325753) baseStart_325753 baseEnd_325753 := by
    simpa [prefixWord, tailWord_325753, baseEnd_325753] using wordTrace_append hprefix tailTrace_325753
  have hstable : (prefixWord ++ tailWord_325753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325753).length < 2 ^ (prefixWord ++ tailWord_325753).sum := by decide
  have hdescent : baseEnd_325753 < baseStart_325753 := by decide
  rcases family_descends (prefixWord ++ tailWord_325753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325767 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_325767 : Nat := 118140960795 + 325767 * 2 ^ 59
def prefixEnd_325767 : Nat := 4983230072969 + 3 ^ 40 * 325767 * 2
def baseEnd_325767 : Nat := 167275052373332168814331

theorem tailTrace_325767 : CollatzResearch.WordTrace tailWord_325767 prefixEnd_325767 167275052373332168814331 := by
  unfold tailWord_325767
  simp only [CollatzResearch.WordTrace]
  refine ⟨11881698610809270419255555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7921132407206180279503703 11881698610809270419255555)
  ·
    refine ⟨17822547916213905628883333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11881698610809270419255555 17822547916213905628883333)
    ·
      refine ⟨3341727734290107305415625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17822547916213905628883333 3341727734290107305415625)
      ·
        refine ⟨2506295800717580479061719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3341727734290107305415625 2506295800717580479061719)
        ·
          refine ⟨3759443701076370718592579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2506295800717580479061719 3759443701076370718592579)
          ·
            refine ⟨5639165551614556077888869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3759443701076370718592579 5639165551614556077888869)
            ·
              refine ⟨1057343540927729264604163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5639165551614556077888869 1057343540927729264604163)
              ·
                refine ⟨1586015311391593896906245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057343540927729264604163 1586015311391593896906245)
                ·
                  refine ⟨297377870885923855669921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586015311391593896906245 297377870885923855669921)
                  ·
                    refine ⟨223033403164442891752441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 297377870885923855669921 223033403164442891752441)
                    ·
                      refine ⟨167275052373332168814331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223033403164442891752441 167275052373332168814331)
                      ·
                        rfl

theorem cell23_325767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_325767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325767 prefixEnd_325767 := by exact prefixLift 325767
  have htrace : WordTrace (prefixWord ++ tailWord_325767) baseStart_325767 baseEnd_325767 := by
    simpa [prefixWord, tailWord_325767, baseEnd_325767] using wordTrace_append hprefix tailTrace_325767
  have hstable : (prefixWord ++ tailWord_325767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325767).length < 2 ^ (prefixWord ++ tailWord_325767).sum := by decide
  have hdescent : baseEnd_325767 < baseStart_325767 := by decide
  rcases family_descends (prefixWord ++ tailWord_325767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325782 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_325782 : Nat := 118140960795 + 325782 * 2 ^ 59
def prefixEnd_325782 : Nat := 4983230072969 + 3 ^ 40 * 325782 * 2
def baseEnd_325782 : Nat := 167282754583149610126763

theorem tailTrace_325782 : CollatzResearch.WordTrace tailWord_325782 prefixEnd_325782 167282754583149610126763 := by
  unfold tailWord_325782
  simp only [CollatzResearch.WordTrace]
  refine ⟨742640356609682998815725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7921497137169951987367733 742640356609682998815725)
  ·
    refine ⟨278490133728631124555897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 742640356609682998815725 278490133728631124555897)
    ·
      refine ⟨208867600296473343416923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 278490133728631124555897 208867600296473343416923)
      ·
        refine ⟨313301400444710015125385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208867600296473343416923 313301400444710015125385)
        ·
          refine ⟨234976050333532511344039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313301400444710015125385 234976050333532511344039)
          ·
            refine ⟨352464075500298767016059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234976050333532511344039 352464075500298767016059)
            ·
              refine ⟨528696113250448150524089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352464075500298767016059 528696113250448150524089)
              ·
                refine ⟨396522084937836112893067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528696113250448150524089 396522084937836112893067)
                ·
                  refine ⟨594783127406754169339601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396522084937836112893067 594783127406754169339601)
                  ·
                    refine ⟨446087345555065627004701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 594783127406754169339601 446087345555065627004701)
                    ·
                      refine ⟨167282754583149610126763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 446087345555065627004701 167282754583149610126763)
                      ·
                        rfl

theorem cell23_325782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_325782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325782 prefixEnd_325782 := by exact prefixLift 325782
  have htrace : WordTrace (prefixWord ++ tailWord_325782) baseStart_325782 baseEnd_325782 := by
    simpa [prefixWord, tailWord_325782, baseEnd_325782] using wordTrace_append hprefix tailTrace_325782
  have hstable : (prefixWord ++ tailWord_325782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325782).length < 2 ^ (prefixWord ++ tailWord_325782).sum := by decide
  have hdescent : baseEnd_325782 < baseStart_325782 := by decide
  rcases family_descends (prefixWord ++ tailWord_325782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325823 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 4]
def baseStart_325823 : Nat := 118140960795 + 325823 * 2 ^ 59
def prefixEnd_325823 : Nat := 4983230072969 + 3 ^ 40 * 325823 * 2
def baseEnd_325823 : Nat := 167303807289983949714073

theorem tailTrace_325823 : CollatzResearch.WordTrace tailWord_325823 prefixEnd_325823 167303807289983949714073 := by
  unfold tailWord_325823
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883741098606391983294123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7922494065737594655529415 11883741098606391983294123)
  ·
    refine ⟨17825611647909587974941185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11883741098606391983294123 17825611647909587974941185)
    ·
      refine ⟨13369208735932190981205889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17825611647909587974941185 13369208735932190981205889)
      ·
        refine ⟨10026906551949143235904417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13369208735932190981205889 10026906551949143235904417)
        ·
          refine ⟨7520179913961857426928313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10026906551949143235904417 7520179913961857426928313)
          ·
            refine ⟨5640134935471393070196235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7520179913961857426928313 5640134935471393070196235)
            ·
              refine ⟨8460202403207089605294353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640134935471393070196235 8460202403207089605294353)
              ·
                refine ⟨6345151802405317203970765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8460202403207089605294353 6345151802405317203970765)
                ·
                  refine ⟨2379431925901993951489037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6345151802405317203970765 2379431925901993951489037)
                  ·
                    refine ⟨892286972213247731808389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2379431925901993951489037 892286972213247731808389)
                    ·
                      refine ⟨167303807289983949714073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 892286972213247731808389 167303807289983949714073)
                      ·
                        rfl

theorem cell23_325823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_325823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325823 prefixEnd_325823 := by exact prefixLift 325823
  have htrace : WordTrace (prefixWord ++ tailWord_325823) baseStart_325823 baseEnd_325823 := by
    simpa [prefixWord, tailWord_325823, baseEnd_325823] using wordTrace_append hprefix tailTrace_325823
  have hstable : (prefixWord ++ tailWord_325823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325823).length < 2 ^ (prefixWord ++ tailWord_325823).sum := by decide
  have hdescent : baseEnd_325823 < baseStart_325823 := by decide
  rcases family_descends (prefixWord ++ tailWord_325823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325824 : List Nat := [2, 1, 1, 2, 5, 3, 2, 2, 5]
def baseStart_325824 : Nat := 118140960795 + 325824 * 2 ^ 59
def prefixEnd_325824 : Nat := 4983230072969 + 3 ^ 40 * 325824 * 2
def baseEnd_325824 : Nat := 18589368974515382866841

theorem tailTrace_325824 : CollatzResearch.WordTrace tailWord_325824 prefixEnd_325824 18589368974515382866841 := by
  unfold tailWord_325824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941888785801384577040263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7922518381068512769387017 5941888785801384577040263)
  ·
    refine ⟨8912833178702076865560395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5941888785801384577040263 8912833178702076865560395)
    ·
      refine ⟨13369249768053115298340593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8912833178702076865560395 13369249768053115298340593)
      ·
        refine ⟨10026937326039836473755445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13369249768053115298340593 10026937326039836473755445)
        ·
          refine ⟨940025374316234669414573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10026937326039836473755445 940025374316234669414573)
          ·
            refine ⟨352509515368588001030465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 940025374316234669414573 352509515368588001030465)
            ·
              refine ⟨264382136526441000772849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352509515368588001030465 264382136526441000772849)
              ·
                refine ⟨198286602394830750579637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264382136526441000772849 198286602394830750579637)
                ·
                  refine ⟨18589368974515382866841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198286602394830750579637 18589368974515382866841)
                  ·
                    rfl

theorem cell23_325824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2, 5].length) (baseStart_325824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325824 prefixEnd_325824 := by exact prefixLift 325824
  have htrace : WordTrace (prefixWord ++ tailWord_325824) baseStart_325824 baseEnd_325824 := by
    simpa [prefixWord, tailWord_325824, baseEnd_325824] using wordTrace_append hprefix tailTrace_325824
  have hstable : (prefixWord ++ tailWord_325824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325824).length < 2 ^ (prefixWord ++ tailWord_325824).sum := by decide
  have hdescent : baseEnd_325824 < baseStart_325824 := by decide
  rcases family_descends (prefixWord ++ tailWord_325824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325850 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_325850 : Nat := 118140960795 + 325850 * 2 ^ 59
def prefixEnd_325850 : Nat := 4983230072969 + 3 ^ 40 * 325850 * 2
def baseEnd_325850 : Nat := 55772557089218448025483

theorem tailTrace_325850 : CollatzResearch.WordTrace tailWord_325850 prefixEnd_325850 55772557089218448025483 := by
  unfold tailWord_325850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971181467377143898631751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7923150579672383729684669 2971181467377143898631751)
  ·
    refine ⟨4456772201065715847947627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2971181467377143898631751 4456772201065715847947627)
    ·
      refine ⟨6685158301598573771921441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4456772201065715847947627 6685158301598573771921441)
      ·
        refine ⟨5013868726198930328941081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6685158301598573771921441 5013868726198930328941081)
        ·
          refine ⟨3760401544649197746705811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5013868726198930328941081 3760401544649197746705811)
          ·
            refine ⟨5640602316973796620058717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760401544649197746705811 5640602316973796620058717)
            ·
              refine ⟨2115225868865173732522019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5640602316973796620058717 2115225868865173732522019)
              ·
                refine ⟨3172838803297760598783029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115225868865173732522019 3172838803297760598783029)
                ·
                  refine ⟨297453637809165056135909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3172838803297760598783029 297453637809165056135909)
                  ·
                    refine ⟨55772557089218448025483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297453637809165056135909 55772557089218448025483)
                    ·
                      rfl

theorem cell23_325850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_325850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325850 prefixEnd_325850 := by exact prefixLift 325850
  have htrace : WordTrace (prefixWord ++ tailWord_325850) baseStart_325850 baseEnd_325850 := by
    simpa [prefixWord, tailWord_325850, baseEnd_325850] using wordTrace_append hprefix tailTrace_325850
  have hstable : (prefixWord ++ tailWord_325850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325850).length < 2 ^ (prefixWord ++ tailWord_325850).sum := by decide
  have hdescent : baseEnd_325850 < baseStart_325850 := by decide
  rcases family_descends (prefixWord ++ tailWord_325850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325858 : List Nat := [3, 3, 4, 1, 1, 1, 2, 3, 5]
def baseStart_325858 : Nat := 118140960795 + 325858 * 2 ^ 59
def prefixEnd_325858 : Nat := 4983230072969 + 3 ^ 40 * 325858 * 2
def baseEnd_325858 : Nat := 18591308790321256975157

theorem tailTrace_325858 : CollatzResearch.WordTrace tailWord_325858 prefixEnd_325858 18591308790321256975157 := by
  unfold tailWord_325858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971254413369898240204557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7923345102319728640545485 2971254413369898240204557)
  ·
    refine ⟨1114220405013711840076709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2971254413369898240204557 1114220405013711840076709)
    ·
      refine ⟨208916325940070970014383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1114220405013711840076709 208916325940070970014383)
      ·
        refine ⟨313374488910106455021575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208916325940070970014383 313374488910106455021575)
        ·
          refine ⟨470061733365159682532363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313374488910106455021575 470061733365159682532363)
          ·
            refine ⟨705092600047739523798545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470061733365159682532363 705092600047739523798545)
            ·
              refine ⟨528819450035804642848909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705092600047739523798545 528819450035804642848909)
              ·
                refine ⟨198307293763426741068341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528819450035804642848909 198307293763426741068341)
                ·
                  refine ⟨18591308790321256975157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198307293763426741068341 18591308790321256975157)
                  ·
                    rfl

theorem cell23_325858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_325858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325858 prefixEnd_325858 := by exact prefixLift 325858
  have htrace : WordTrace (prefixWord ++ tailWord_325858) baseStart_325858 baseEnd_325858 := by
    simpa [prefixWord, tailWord_325858, baseEnd_325858] using wordTrace_append hprefix tailTrace_325858
  have hstable : (prefixWord ++ tailWord_325858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325858).length < 2 ^ (prefixWord ++ tailWord_325858).sum := by decide
  have hdescent : baseEnd_325858 < baseStart_325858 := by decide
  rcases family_descends (prefixWord ++ tailWord_325858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325884 : List Nat := [2, 2, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_325884 : Nat := 118140960795 + 325884 * 2 ^ 59
def prefixEnd_325884 : Nat := 4983230072969 + 3 ^ 40 * 325884 * 2
def baseEnd_325884 : Nat := 55778376536636070350431

theorem tailTrace_325884 : CollatzResearch.WordTrace tailWord_325884 prefixEnd_325884 55778376536636070350431 := by
  unfold tailWord_325884
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942982975692699700632353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7923977300923599600843137 5942982975692699700632353)
  ·
    refine ⟨4457237231769524775474265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5942982975692699700632353 4457237231769524775474265)
    ·
      refine ⟨3342927923827143581605699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4457237231769524775474265 3342927923827143581605699)
      ·
        refine ⟨5014391885740715372408549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342927923827143581605699 5014391885740715372408549)
        ·
          refine ⟨940198478576384132326603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5014391885740715372408549 940198478576384132326603)
          ·
            refine ⟨1410297717864576198489905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940198478576384132326603 1410297717864576198489905)
            ·
              refine ⟨1057723288398432148867429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410297717864576198489905 1057723288398432148867429)
              ·
                refine ⟨198323116574706027912643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1057723288398432148867429 198323116574706027912643)
                ·
                  refine ⟨297484674862059041868965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198323116574706027912643 297484674862059041868965)
                  ·
                    refine ⟨55778376536636070350431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297484674862059041868965 55778376536636070350431)
                    ·
                      rfl

theorem cell23_325884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_325884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325884 prefixEnd_325884 := by exact prefixLift 325884
  have htrace : WordTrace (prefixWord ++ tailWord_325884) baseStart_325884 baseEnd_325884 := by
    simpa [prefixWord, tailWord_325884, baseEnd_325884] using wordTrace_append hprefix tailTrace_325884
  have hstable : (prefixWord ++ tailWord_325884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325884).length < 2 ^ (prefixWord ++ tailWord_325884).sum := by decide
  have hdescent : baseEnd_325884 < baseStart_325884 := by decide
  rcases family_descends (prefixWord ++ tailWord_325884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325893 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_325893 : Nat := 118140960795 + 325893 * 2 ^ 59
def prefixEnd_325893 : Nat := 4983230072969 + 3 ^ 40 * 325893 * 2
def baseEnd_325893 : Nat := 55779916978599558612917

theorem tailTrace_325893 : CollatzResearch.WordTrace tailWord_325893 prefixEnd_325893 55779916978599558612917 := by
  unfold tailWord_325893
  simp only [CollatzResearch.WordTrace]
  refine ⟨11886294208352793938342333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7924196138901862625561555 11886294208352793938342333)
  ·
    refine ⟨4457360328132297726878375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11886294208352793938342333 4457360328132297726878375)
    ·
      refine ⟨6686040492198446590317563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4457360328132297726878375 6686040492198446590317563)
      ·
        refine ⟨10029060738297669885476345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6686040492198446590317563 10029060738297669885476345)
        ·
          refine ⟨7521795553723252414107259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10029060738297669885476345 7521795553723252414107259)
          ·
            refine ⟨11282693330584878621160889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7521795553723252414107259 11282693330584878621160889)
            ·
              refine ⟨8462019997938658965870667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11282693330584878621160889 8462019997938658965870667)
              ·
                refine ⟨12693029996907988448806001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462019997938658965870667 12693029996907988448806001)
                ·
                  refine ⟨9519772497680991336604501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12693029996907988448806001 9519772497680991336604501)
                  ·
                    refine ⟨55779916978599558612917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9519772497680991336604501 55779916978599558612917)
                    ·
                      rfl

theorem cell23_325893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_325893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325893 prefixEnd_325893 := by exact prefixLift 325893
  have htrace : WordTrace (prefixWord ++ tailWord_325893) baseStart_325893 baseEnd_325893 := by
    simpa [prefixWord, tailWord_325893, baseEnd_325893] using wordTrace_append hprefix tailTrace_325893
  have hstable : (prefixWord ++ tailWord_325893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325893).length < 2 ^ (prefixWord ++ tailWord_325893).sum := by decide
  have hdescent : baseEnd_325893 < baseStart_325893 := by decide
  rcases family_descends (prefixWord ++ tailWord_325893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325897 : List Nat := [1, 2, 1, 1, 3, 5, 3, 1, 6]
def baseStart_325897 : Nat := 118140960795 + 325897 * 2 ^ 59
def prefixEnd_325897 : Nat := 4983230072969 + 3 ^ 40 * 325897 * 2
def baseEnd_325897 : Nat := 18593533873157406687637

theorem tailTrace_325897 : CollatzResearch.WordTrace tailWord_325897 prefixEnd_325897 18593533873157406687637 := by
  unfold tailWord_325897
  simp only [CollatzResearch.WordTrace]
  refine ⟨11886440100338302621487945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7924293400225535080991963 11886440100338302621487945)
  ·
    refine ⟨8914830075253726966115959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11886440100338302621487945 8914830075253726966115959)
    ·
      refine ⟨13372245112880590449173939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8914830075253726966115959 13372245112880590449173939)
      ·
        refine ⟨20058367669320885673760909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13372245112880590449173939 20058367669320885673760909)
        ·
          refine ⟨7521887875995332127660341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20058367669320885673760909 7521887875995332127660341)
          ·
            refine ⟨705176988374562386968157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7521887875995332127660341 705176988374562386968157)
            ·
              refine ⟨264441370640460895113059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705176988374562386968157 264441370640460895113059)
              ·
                refine ⟨396662055960691342669589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264441370640460895113059 396662055960691342669589)
                ·
                  refine ⟨18593533873157406687637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 396662055960691342669589 18593533873157406687637)
                  ·
                    rfl

theorem cell23_325897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 6].length) (baseStart_325897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325897 prefixEnd_325897 := by exact prefixLift 325897
  have htrace : WordTrace (prefixWord ++ tailWord_325897) baseStart_325897 baseEnd_325897 := by
    simpa [prefixWord, tailWord_325897, baseEnd_325897] using wordTrace_append hprefix tailTrace_325897
  have hstable : (prefixWord ++ tailWord_325897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325897).length < 2 ^ (prefixWord ++ tailWord_325897).sum := by decide
  have hdescent : baseEnd_325897 < baseStart_325897 := by decide
  rcases family_descends (prefixWord ++ tailWord_325897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325903 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 7]
def baseStart_325903 : Nat := 118140960795 + 325903 * 2 ^ 59
def prefixEnd_325903 : Nat := 4983230072969 + 3 ^ 40 * 325903 * 2
def baseEnd_325903 : Nat := 167344885742343636713705

theorem tailTrace_325903 : CollatzResearch.WordTrace tailWord_325903 prefixEnd_325903 167344885742343636713705 := by
  unfold tailWord_325903
  simp only [CollatzResearch.WordTrace]
  refine ⟨11886658938316565646206363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7924439292211043764137575 11886658938316565646206363)
  ·
    refine ⟨17829988407474848469309545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11886658938316565646206363 17829988407474848469309545)
    ·
      refine ⟨13372491305606136351982159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17829988407474848469309545 13372491305606136351982159)
      ·
        refine ⟨20058736958409204527973239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13372491305606136351982159 20058736958409204527973239)
        ·
          refine ⟨30088105437613806791959859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20058736958409204527973239 30088105437613806791959859)
          ·
            refine ⟨45132158156420710187939789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30088105437613806791959859 45132158156420710187939789)
            ·
              refine ⟨16924559308657766320477421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45132158156420710187939789 16924559308657766320477421)
              ·
                refine ⟨6346709740746662370179033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16924559308657766320477421 6346709740746662370179033)
                ·
                  refine ⟨4760032305559996777634275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6346709740746662370179033 4760032305559996777634275)
                  ·
                    refine ⟨7140048458339995166451413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4760032305559996777634275 7140048458339995166451413)
                    ·
                      refine ⟨167344885742343636713705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7140048458339995166451413 167344885742343636713705)
                      ·
                        rfl

theorem cell23_325903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_325903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325903 prefixEnd_325903 := by exact prefixLift 325903
  have htrace : WordTrace (prefixWord ++ tailWord_325903) baseStart_325903 baseEnd_325903 := by
    simpa [prefixWord, tailWord_325903, baseEnd_325903] using wordTrace_append hprefix tailTrace_325903
  have hstable : (prefixWord ++ tailWord_325903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325903).length < 2 ^ (prefixWord ++ tailWord_325903).sum := by decide
  have hdescent : baseEnd_325903 < baseStart_325903 := by decide
  rcases family_descends (prefixWord ++ tailWord_325903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325918 : List Nat := [4, 3, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_325918 : Nat := 118140960795 + 325918 * 2 ^ 59
def prefixEnd_325918 : Nat := 4983230072969 + 3 ^ 40 * 325918 * 2
def baseEnd_325918 : Nat := 55784195984053692675379

theorem tailTrace_325918 : CollatzResearch.WordTrace tailWord_325918 prefixEnd_325918 55784195984053692675379 := by
  unfold tailWord_325918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485900754157777901000301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7924804022174815472001605 1485900754157777901000301)
  ·
    refine ⟨557212782809166712875113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1485900754157777901000301 557212782809166712875113)
    ·
      refine ⟨417909587106875034656335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 557212782809166712875113 417909587106875034656335)
      ·
        refine ⟨626864380660312551984503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417909587106875034656335 626864380660312551984503)
        ·
          refine ⟨940296570990468827976755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626864380660312551984503 940296570990468827976755)
          ·
            refine ⟨1410444856485703241965133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940296570990468827976755 1410444856485703241965133)
            ·
              refine ⟨528916821182138715736925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1410444856485703241965133 528916821182138715736925)
              ·
                refine ⟨198343807943302018401347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 528916821182138715736925 198343807943302018401347)
                ·
                  refine ⟨297515711914953027602021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198343807943302018401347 297515711914953027602021)
                  ·
                    refine ⟨55784195984053692675379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 297515711914953027602021 55784195984053692675379)
                    ·
                      rfl

theorem cell23_325918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_325918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325918 prefixEnd_325918 := by exact prefixLift 325918
  have htrace : WordTrace (prefixWord ++ tailWord_325918) baseStart_325918 baseEnd_325918 := by
    simpa [prefixWord, tailWord_325918, baseEnd_325918] using wordTrace_append hprefix tailTrace_325918
  have hstable : (prefixWord ++ tailWord_325918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325918).length < 2 ^ (prefixWord ++ tailWord_325918).sum := by decide
  have hdescent : baseEnd_325918 < baseStart_325918 := by decide
  rcases family_descends (prefixWord ++ tailWord_325918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325960 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_325960 : Nat := 118140960795 + 325960 * 2 ^ 59
def prefixEnd_325960 : Nat := 4983230072969 + 3 ^ 40 * 325960 * 2
def baseEnd_325960 : Nat := 167374154139649913700943

theorem tailTrace_325960 : CollatzResearch.WordTrace tailWord_325960 prefixEnd_325960 167374154139649913700943 := by
  unfold tailWord_325960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944368949555032190515667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7925825266073376254020889 5944368949555032190515667)
  ·
    refine ⟨8916553424332548285773501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5944368949555032190515667 8916553424332548285773501)
    ·
      refine ⟨3343707534124705607165063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8916553424332548285773501 3343707534124705607165063)
      ·
        refine ⟨5015561301187058410747595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3343707534124705607165063 5015561301187058410747595)
        ·
          refine ⟨7523341951780587616121393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5015561301187058410747595 7523341951780587616121393)
          ·
            refine ⟨5642506463835440712091045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7523341951780587616121393 5642506463835440712091045)
            ·
              refine ⟨1057969961969145133517071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5642506463835440712091045 1057969961969145133517071)
              ·
                refine ⟨1586954942953717700275607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057969961969145133517071 1586954942953717700275607)
                ·
                  refine ⟨2380432414430576550413411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586954942953717700275607 2380432414430576550413411)
                  ·
                    refine ⟨3570648621645864825620117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2380432414430576550413411 3570648621645864825620117)
                    ·
                      refine ⟨167374154139649913700943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3570648621645864825620117 167374154139649913700943)
                      ·
                        rfl

theorem cell23_325960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_325960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325960 prefixEnd_325960 := by exact prefixLift 325960
  have htrace : WordTrace (prefixWord ++ tailWord_325960) baseStart_325960 baseEnd_325960 := by
    simpa [prefixWord, tailWord_325960, baseEnd_325960] using wordTrace_append hprefix tailTrace_325960
  have hstable : (prefixWord ++ tailWord_325960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325960).length < 2 ^ (prefixWord ++ tailWord_325960).sum := by decide
  have hdescent : baseEnd_325960 < baseStart_325960 := by decide
  rcases family_descends (prefixWord ++ tailWord_325960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325964 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 5, 2, 2]
def baseStart_325964 : Nat := 118140960795 + 325964 * 2 ^ 59
def prefixEnd_325964 : Nat := 4983230072969 + 3 ^ 40 * 325964 * 2
def baseEnd_325964 : Nat := 167376208062267898050925

theorem tailTrace_325964 : CollatzResearch.WordTrace tailWord_325964 prefixEnd_325964 167376208062267898050925 := by
  unfold tailWord_325964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944441895547786532088473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7925922527397048709451297 5944441895547786532088473)
  ·
    refine ⟨4458331421660839899066355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5944441895547786532088473 4458331421660839899066355)
    ·
      refine ⟨6687497132491259848599533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4458331421660839899066355 6687497132491259848599533)
      ·
        refine ⟨2507811424684222443224825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6687497132491259848599533 2507811424684222443224825)
        ·
          refine ⟨1880858568513166832418619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2507811424684222443224825 1880858568513166832418619)
          ·
            refine ⟨2821287852769750248627929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880858568513166832418619 2821287852769750248627929)
            ·
              refine ⟨2115965889577312686470947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821287852769750248627929 2115965889577312686470947)
              ·
                refine ⟨3173948834365969029706421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115965889577312686470947 3173948834365969029706421)
                ·
                  refine ⟨297557703221809596534977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3173948834365969029706421 297557703221809596534977)
                  ·
                    refine ⟨223168277416357197401233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 297557703221809596534977 223168277416357197401233)
                    ·
                      refine ⟨167376208062267898050925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223168277416357197401233 167376208062267898050925)
                      ·
                        rfl

theorem cell23_325964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_325964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325964 prefixEnd_325964 := by exact prefixLift 325964
  have htrace : WordTrace (prefixWord ++ tailWord_325964) baseStart_325964 baseEnd_325964 := by
    simpa [prefixWord, tailWord_325964, baseEnd_325964] using wordTrace_append hprefix tailTrace_325964
  have hstable : (prefixWord ++ tailWord_325964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325964).length < 2 ^ (prefixWord ++ tailWord_325964).sum := by decide
  have hdescent : baseEnd_325964 < baseStart_325964 := by decide
  rcases family_descends (prefixWord ++ tailWord_325964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325967 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 3]
def baseStart_325967 : Nat := 118140960795 + 325967 * 2 ^ 59
def prefixEnd_325967 : Nat := 4983230072969 + 3 ^ 40 * 325967 * 2
def baseEnd_325967 : Nat := 167377748504231386313411

theorem tailTrace_325967 : CollatzResearch.WordTrace tailWord_325967 prefixEnd_325967 167377748504231386313411 := by
  unfold tailWord_325967
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888993210084704576536155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7925995473389803051024103 11888993210084704576536155)
  ·
    refine ⟨17833489815127056864804233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11888993210084704576536155 17833489815127056864804233)
    ·
      refine ⟨13375117361345292648603175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17833489815127056864804233 13375117361345292648603175)
      ·
        refine ⟨20062676042017938972904763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13375117361345292648603175 20062676042017938972904763)
        ·
          refine ⟨30094014063026908459357145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20062676042017938972904763 30094014063026908459357145)
          ·
            refine ⟨22570510547270181344517859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30094014063026908459357145 22570510547270181344517859)
            ·
              refine ⟨33855765820905272016776789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22570510547270181344517859 33855765820905272016776789)
              ·
                refine ⟨396747255713733656446603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 33855765820905272016776789 396747255713733656446603)
                ·
                  refine ⟨595120883570600484669905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 396747255713733656446603 595120883570600484669905)
                  ·
                    refine ⟨446340662677950363502429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595120883570600484669905 446340662677950363502429)
                    ·
                      refine ⟨167377748504231386313411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 446340662677950363502429 167377748504231386313411)
                      ·
                        rfl

theorem cell23_325967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 2, 3].length) (baseStart_325967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325967 prefixEnd_325967 := by exact prefixLift 325967
  have htrace : WordTrace (prefixWord ++ tailWord_325967) baseStart_325967 baseEnd_325967 := by
    simpa [prefixWord, tailWord_325967, baseEnd_325967] using wordTrace_append hprefix tailTrace_325967
  have hstable : (prefixWord ++ tailWord_325967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325967).length < 2 ^ (prefixWord ++ tailWord_325967).sum := by decide
  have hdescent : baseEnd_325967 < baseStart_325967 := by decide
  rcases family_descends (prefixWord ++ tailWord_325967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325970 : List Nat := [3, 2, 2, 1, 1, 1, 4, 9]
def baseStart_325970 : Nat := 118140960795 + 325970 * 2 ^ 59
def prefixEnd_325970 : Nat := 4983230072969 + 3 ^ 40 * 325970 * 2
def baseEnd_325970 : Nat := 6199232923933143502811

theorem tailTrace_325970 : CollatzResearch.WordTrace tailWord_325970 prefixEnd_325970 6199232923933143502811 := by
  unfold tailWord_325970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972275657268459022223841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7926068419382557392596909 2972275657268459022223841)
  ·
    refine ⟨2229206742951344266667881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2972275657268459022223841 2229206742951344266667881)
    ·
      refine ⟨1671905057213508200000911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2229206742951344266667881 1671905057213508200000911)
      ·
        refine ⟨2507857585820262300001367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671905057213508200000911 2507857585820262300001367)
        ·
          refine ⟨3761786378730393450002051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507857585820262300001367 3761786378730393450002051)
          ·
            refine ⟨5642679568095590175003077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761786378730393450002051 5642679568095590175003077)
            ·
              refine ⟨1058002419017923157813077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5642679568095590175003077 1058002419017923157813077)
              ·
                refine ⟨6199232923933143502811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1058002419017923157813077 6199232923933143502811)
                ·
                  rfl

theorem cell23_325970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 9].length) (baseStart_325970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325970 prefixEnd_325970 := by exact prefixLift 325970
  have htrace : WordTrace (prefixWord ++ tailWord_325970) baseStart_325970 baseEnd_325970 := by
    simpa [prefixWord, tailWord_325970, baseEnd_325970] using wordTrace_append hprefix tailTrace_325970
  have hstable : (prefixWord ++ tailWord_325970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325970).length < 2 ^ (prefixWord ++ tailWord_325970).sum := by decide
  have hdescent : baseEnd_325970 < baseStart_325970 := by decide
  rcases family_descends (prefixWord ++ tailWord_325970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325984 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5]
def baseStart_325984 : Nat := 118140960795 + 325984 * 2 ^ 59
def prefixEnd_325984 : Nat := 4983230072969 + 3 ^ 40 * 325984 * 2
def baseEnd_325984 : Nat := 167386477675357819800833

theorem tailTrace_325984 : CollatzResearch.WordTrace tailWord_325984 prefixEnd_325984 167386477675357819800833 := by
  unfold tailWord_325984
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944806625511558239952503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7926408834015410986603337 5944806625511558239952503)
  ·
    refine ⟨8917209938267337359928755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5944806625511558239952503 8917209938267337359928755)
    ·
      refine ⟨13375814907401006039893133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8917209938267337359928755 13375814907401006039893133)
      ·
        refine ⟨5015930590275377264959925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13375814907401006039893133 5015930590275377264959925)
        ·
          refine ⟨470243492838316618589993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5015930590275377264959925 470243492838316618589993)
          ·
            refine ⟨352682619628737463942495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470243492838316618589993 352682619628737463942495)
            ·
              refine ⟨529023929443106195913743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352682619628737463942495 529023929443106195913743)
              ·
                refine ⟨793535894164659293870615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529023929443106195913743 793535894164659293870615)
                ·
                  refine ⟨1190303841246988940805923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793535894164659293870615 1190303841246988940805923)
                  ·
                    refine ⟨1785455761870483411208885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1190303841246988940805923 1785455761870483411208885)
                    ·
                      refine ⟨167386477675357819800833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1785455761870483411208885 167386477675357819800833)
                      ·
                        rfl

theorem cell23_325984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_325984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325984 prefixEnd_325984 := by exact prefixLift 325984
  have htrace : WordTrace (prefixWord ++ tailWord_325984) baseStart_325984 baseEnd_325984 := by
    simpa [prefixWord, tailWord_325984, baseEnd_325984] using wordTrace_append hprefix tailTrace_325984
  have hstable : (prefixWord ++ tailWord_325984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325984).length < 2 ^ (prefixWord ++ tailWord_325984).sum := by decide
  have hdescent : baseEnd_325984 < baseStart_325984 := by decide
  rcases family_descends (prefixWord ++ tailWord_325984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_325997 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_325997 : Nat := 118140960795 + 325997 * 2 ^ 59
def prefixEnd_325997 : Nat := 4983230072969 + 3 ^ 40 * 325997 * 2
def baseEnd_325997 : Nat := 167393152923866268938273

theorem tailTrace_325997 : CollatzResearch.WordTrace tailWord_325997 prefixEnd_325997 167393152923866268938273 := by
  unfold tailWord_325997
  simp only [CollatzResearch.WordTrace]
  refine ⟨11890087399976019700128245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7926724933317346466752163 11890087399976019700128245)
  ·
    refine ⟨1114695693747751846887023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11890087399976019700128245 1114695693747751846887023)
    ·
      refine ⟨1672043540621627770330535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114695693747751846887023 1672043540621627770330535)
      ·
        refine ⟨2508065310932441655495803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672043540621627770330535 2508065310932441655495803)
        ·
          refine ⟨3762097966398662483243705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508065310932441655495803 3762097966398662483243705)
          ·
            refine ⟨2821573474798996862432779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3762097966398662483243705 2821573474798996862432779)
            ·
              refine ⟨4232360212198495293649169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821573474798996862432779 4232360212198495293649169)
              ·
                refine ⟨3174270159148871470236877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4232360212198495293649169 3174270159148871470236877)
                ·
                  refine ⟨1190351309680826801338829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3174270159148871470236877 1190351309680826801338829)
                  ·
                    refine ⟨446381741130310050502061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190351309680826801338829 446381741130310050502061)
                    ·
                      refine ⟨167393152923866268938273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 446381741130310050502061 167393152923866268938273)
                      ·
                        rfl

theorem cell23_325997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_325997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_325997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_325997 prefixEnd_325997 := by exact prefixLift 325997
  have htrace : WordTrace (prefixWord ++ tailWord_325997) baseStart_325997 baseEnd_325997 := by
    simpa [prefixWord, tailWord_325997, baseEnd_325997] using wordTrace_append hprefix tailTrace_325997
  have hstable : (prefixWord ++ tailWord_325997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_325997).length < 2 ^ (prefixWord ++ tailWord_325997).sum := by decide
  have hdescent : baseEnd_325997 < baseStart_325997 := by decide
  rcases family_descends (prefixWord ++ tailWord_325997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326000 : List Nat := [2, 1, 1, 1, 4, 3, 1, 1, 2, 7]
def baseStart_326000 : Nat := 118140960795 + 326000 * 2 ^ 59
def prefixEnd_326000 : Nat := 4983230072969 + 3 ^ 40 * 326000 * 2
def baseEnd_326000 : Nat := 55798231121943252400253

theorem tailTrace_326000 : CollatzResearch.WordTrace tailWord_326000 prefixEnd_326000 55798231121943252400253 := by
  unfold tailWord_326000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945098409482575606243727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7926797879310100808324969 5945098409482575606243727)
  ·
    refine ⟨8917647614223863409365591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5945098409482575606243727 8917647614223863409365591)
    ·
      refine ⟨13376471421335795114048387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8917647614223863409365591 13376471421335795114048387)
      ·
        refine ⟨20064707132003692671072581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13376471421335795114048387 20064707132003692671072581)
        ·
          refine ⟨3762132587250692375826109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20064707132003692671072581 3762132587250692375826109)
          ·
            refine ⟨1410799720219009640934791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3762132587250692375826109 1410799720219009640934791)
            ·
              refine ⟨2116199580328514461402187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410799720219009640934791 2116199580328514461402187)
              ·
                refine ⟨3174299370492771692103281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116199580328514461402187 3174299370492771692103281)
                ·
                  refine ⟨2380724527869578769077461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3174299370492771692103281 2380724527869578769077461)
                  ·
                    refine ⟨55798231121943252400253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2380724527869578769077461 55798231121943252400253)
                    ·
                      rfl

theorem cell23_326000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_326000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326000 prefixEnd_326000 := by exact prefixLift 326000
  have htrace : WordTrace (prefixWord ++ tailWord_326000) baseStart_326000 baseEnd_326000 := by
    simpa [prefixWord, tailWord_326000, baseEnd_326000] using wordTrace_append hprefix tailTrace_326000
  have hstable : (prefixWord ++ tailWord_326000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326000).length < 2 ^ (prefixWord ++ tailWord_326000).sum := by decide
  have hdescent : baseEnd_326000 < baseStart_326000 := by decide
  rcases family_descends (prefixWord ++ tailWord_326000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326024 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_326024 : Nat := 118140960795 + 326024 * 2 ^ 59
def prefixEnd_326024 : Nat := 4983230072969 + 3 ^ 40 * 326024 * 2
def baseEnd_326024 : Nat := 167407016901537663300649

theorem tailTrace_326024 : CollatzResearch.WordTrace tailWord_326024 prefixEnd_326024 167407016901537663300649 := by
  unfold tailWord_326024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945536085439101655680563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7927381447252135540907417 5945536085439101655680563)
  ·
    refine ⟨8918304128158652483520845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5945536085439101655680563 8918304128158652483520845)
    ·
      refine ⟨3344364048059494681320317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8918304128158652483520845 3344364048059494681320317)
      ·
        refine ⟨1254136518022310505495119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3344364048059494681320317 1254136518022310505495119)
        ·
          refine ⟨1881204777033465758242679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254136518022310505495119 1881204777033465758242679)
          ·
            refine ⟨2821807165550198637364019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881204777033465758242679 2821807165550198637364019)
            ·
              refine ⟨4232710748325297956046029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821807165550198637364019 4232710748325297956046029)
              ·
                refine ⟨1587266530621986733517261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4232710748325297956046029 1587266530621986733517261)
                ·
                  refine ⟨595224948983245025068973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1587266530621986733517261 595224948983245025068973)
                  ·
                    refine ⟨223209355868716884400865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 595224948983245025068973 223209355868716884400865)
                    ·
                      refine ⟨167407016901537663300649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223209355868716884400865 167407016901537663300649)
                      ·
                        rfl

theorem cell23_326024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_326024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326024 prefixEnd_326024 := by exact prefixLift 326024
  have htrace : WordTrace (prefixWord ++ tailWord_326024) baseStart_326024 baseEnd_326024 := by
    simpa [prefixWord, tailWord_326024, baseEnd_326024] using wordTrace_append hprefix tailTrace_326024
  have hstable : (prefixWord ++ tailWord_326024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326024).length < 2 ^ (prefixWord ++ tailWord_326024).sum := by decide
  have hdescent : baseEnd_326024 < baseStart_326024 := by decide
  rcases family_descends (prefixWord ++ tailWord_326024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326071 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 1, 4, 2]
def baseStart_326071 : Nat := 118140960795 + 326071 * 2 ^ 59
def prefixEnd_326071 : Nat := 4983230072969 + 3 ^ 40 * 326071 * 2
def baseEnd_326071 : Nat := 167431150492298979412933

theorem tailTrace_326071 : CollatzResearch.WordTrace tailWord_326071 prefixEnd_326071 167431150492298979412933 := by
  unfold tailWord_326071
  simp only [CollatzResearch.WordTrace]
  refine ⟨11892786401707930338322067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7928524267805286892214711 11892786401707930338322067)
  ·
    refine ⟨17839179602561895507483101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11892786401707930338322067 17839179602561895507483101)
    ·
      refine ⟨6689692350960710815306163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17839179602561895507483101 6689692350960710815306163)
      ·
        refine ⟨10034538526441066222959245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6689692350960710815306163 10034538526441066222959245)
        ·
          refine ⟨3762951947415399833609717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10034538526441066222959245 3762951947415399833609717)
          ·
            refine ⟨352776745070193734400911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3762951947415399833609717 352776745070193734400911)
            ·
              refine ⟨529165117605290601601367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352776745070193734400911 529165117605290601601367)
              ·
                refine ⟨793747676407935902402051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529165117605290601601367 793747676407935902402051)
                ·
                  refine ⟨1190621514611903853603077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793747676407935902402051 1190621514611903853603077)
                  ·
                    refine ⟨223241533989731972550577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1190621514611903853603077 223241533989731972550577)
                    ·
                      refine ⟨167431150492298979412933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223241533989731972550577 167431150492298979412933)
                      ·
                        rfl

theorem cell23_326071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_326071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326071 prefixEnd_326071 := by exact prefixLift 326071
  have htrace : WordTrace (prefixWord ++ tailWord_326071) baseStart_326071 baseEnd_326071 := by
    simpa [prefixWord, tailWord_326071, baseEnd_326071] using wordTrace_append hprefix tailTrace_326071
  have hstable : (prefixWord ++ tailWord_326071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326071).length < 2 ^ (prefixWord ++ tailWord_326071).sum := by decide
  have hdescent : baseEnd_326071 < baseStart_326071 := by decide
  rcases family_descends (prefixWord ++ tailWord_326071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326077 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 7]
def baseStart_326077 : Nat := 118140960795 + 326077 * 2 ^ 59
def prefixEnd_326077 : Nat := 4983230072969 + 3 ^ 40 * 326077 * 2
def baseEnd_326077 : Nat := 18603803486247328437545

theorem tailTrace_326077 : CollatzResearch.WordTrace tailWord_326077 prefixEnd_326077 18603803486247328437545 := by
  unfold tailWord_326077
  simp only [CollatzResearch.WordTrace]
  refine ⟨11893005239686193363040485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7928670159790795575360323 11893005239686193363040485)
  ·
    refine ⟨2229938482441161255570091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11893005239686193363040485 2229938482441161255570091)
    ·
      refine ⟨3344907723661741883355137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229938482441161255570091 3344907723661741883355137)
      ·
        refine ⟨2508680792746306412516353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3344907723661741883355137 2508680792746306412516353)
        ·
          refine ⟨1881510594559729809387265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2508680792746306412516353 1881510594559729809387265)
          ·
            refine ⟨1411132945919797357040449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1881510594559729809387265 1411132945919797357040449)
            ·
              refine ⟨1058349709439848017780337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411132945919797357040449 1058349709439848017780337)
              ·
                refine ⟨793762282079886013335253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058349709439848017780337 793762282079886013335253)
                ·
                  refine ⟨18603803486247328437545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 793762282079886013335253 18603803486247328437545)
                  ·
                    rfl

theorem cell23_326077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_326077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326077 prefixEnd_326077 := by exact prefixLift 326077
  have htrace : WordTrace (prefixWord ++ tailWord_326077) baseStart_326077 baseEnd_326077 := by
    simpa [prefixWord, tailWord_326077, baseEnd_326077] using wordTrace_append hprefix tailTrace_326077
  have hstable : (prefixWord ++ tailWord_326077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326077).length < 2 ^ (prefixWord ++ tailWord_326077).sum := by decide
  have hdescent : baseEnd_326077 < baseStart_326077 := by decide
  rcases family_descends (prefixWord ++ tailWord_326077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326111 : List Nat := [1, 1, 2, 3, 3, 3, 3, 2, 5]
def baseStart_326111 : Nat := 118140960795 + 326111 * 2 ^ 59
def prefixEnd_326111 : Nat := 4983230072969 + 3 ^ 40 * 326111 * 2
def baseEnd_326111 : Nat := 18605743302053202545861

theorem tailTrace_326111 : CollatzResearch.WordTrace tailWord_326111 prefixEnd_326111 18605743302053202545861 := by
  unfold tailWord_326111
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894245321563017169778187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7929496881042011446518791 11894245321563017169778187)
  ·
    refine ⟨17841367982344525754667281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11894245321563017169778187 17841367982344525754667281)
    ·
      refine ⟨13381025986758394316000461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17841367982344525754667281 13381025986758394316000461)
      ·
        refine ⟨5017884745034397868500173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13381025986758394316000461 5017884745034397868500173)
        ·
          refine ⟨1881706779387899200687565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5017884745034397868500173 1881706779387899200687565)
          ·
            refine ⟨705640042270462200257837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1881706779387899200687565 705640042270462200257837)
            ·
              refine ⟨264615015851423325096689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705640042270462200257837 264615015851423325096689)
              ·
                refine ⟨198461261888567493822517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264615015851423325096689 198461261888567493822517)
                ·
                  refine ⟨18605743302053202545861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198461261888567493822517 18605743302053202545861)
                  ·
                    rfl

theorem cell23_326111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2, 5].length) (baseStart_326111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326111 prefixEnd_326111 := by exact prefixLift 326111
  have htrace : WordTrace (prefixWord ++ tailWord_326111) baseStart_326111 baseEnd_326111 := by
    simpa [prefixWord, tailWord_326111, baseEnd_326111] using wordTrace_append hprefix tailTrace_326111
  have hstable : (prefixWord ++ tailWord_326111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326111).length < 2 ^ (prefixWord ++ tailWord_326111).sum := by decide
  have hdescent : baseEnd_326111 < baseStart_326111 := by decide
  rcases family_descends (prefixWord ++ tailWord_326111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326127 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_326127 : Nat := 118140960795 + 326127 * 2 ^ 59
def prefixEnd_326127 : Nat := 4983230072969 + 3 ^ 40 * 326127 * 2
def baseEnd_326127 : Nat := 167459905408950760312675

theorem tailTrace_326127 : CollatzResearch.WordTrace tailWord_326127 prefixEnd_326127 167459905408950760312675 := by
  unfold tailWord_326127
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894828889505051902360635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7929885926336701268240423 11894828889505051902360635)
  ·
    refine ⟨17842243334257577853540953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11894828889505051902360635 17842243334257577853540953)
    ·
      refine ⟨13381682500693183390155715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17842243334257577853540953 13381682500693183390155715)
      ·
        refine ⟨20072523751039775085233573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13381682500693183390155715 20072523751039775085233573)
        ·
          refine ⟨3763598203319957828481295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20072523751039775085233573 3763598203319957828481295)
          ·
            refine ⟨5645397304979936742721943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763598203319957828481295 5645397304979936742721943)
            ·
              refine ⟨8468095957469905114082915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645397304979936742721943 8468095957469905114082915)
              ·
                refine ⟨12702143936204857671124373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468095957469905114082915 12702143936204857671124373)
                ·
                  refine ⟨595412997009602703333955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12702143936204857671124373 595412997009602703333955)
                  ·
                    refine ⟨893119495514404055000933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 595412997009602703333955 893119495514404055000933)
                    ·
                      refine ⟨167459905408950760312675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 893119495514404055000933 167459905408950760312675)
                      ·
                        rfl

theorem cell23_326127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_326127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326127 prefixEnd_326127 := by exact prefixLift 326127
  have htrace : WordTrace (prefixWord ++ tailWord_326127) baseStart_326127 baseEnd_326127 := by
    simpa [prefixWord, tailWord_326127, baseEnd_326127] using wordTrace_append hprefix tailTrace_326127
  have hstable : (prefixWord ++ tailWord_326127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326127).length < 2 ^ (prefixWord ++ tailWord_326127).sum := by decide
  have hdescent : baseEnd_326127 < baseStart_326127 := by decide
  rcases family_descends (prefixWord ++ tailWord_326127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326198 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_326198 : Nat := 118140960795 + 326198 * 2 ^ 59
def prefixEnd_326198 : Nat := 4983230072969 + 3 ^ 40 * 326198 * 2
def baseEnd_326198 : Nat := 167496362535419982524849

theorem tailTrace_326198 : CollatzResearch.WordTrace tailWord_326198 prefixEnd_326198 167496362535419982524849 := by
  unfold tailWord_326198
  simp only [CollatzResearch.WordTrace]
  refine ⟨743588654515489439262203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7931612314831887352130165 743588654515489439262203)
  ·
    refine ⟨1115382981773234158893305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 743588654515489439262203 1115382981773234158893305)
    ·
      refine ⟨836537236329925619169979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1115382981773234158893305 836537236329925619169979)
      ·
        refine ⟨1254805854494888428754969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836537236329925619169979 1254805854494888428754969)
        ·
          refine ⟨941104390871166321566227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254805854494888428754969 941104390871166321566227)
          ·
            refine ⟨1411656586306749482349341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941104390871166321566227 1411656586306749482349341)
            ·
              refine ⟨529371219865031055881003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1411656586306749482349341 529371219865031055881003)
              ·
                refine ⟨794056829797546583821505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529371219865031055881003 794056829797546583821505)
                ·
                  refine ⟨595542622348159937866129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 794056829797546583821505 595542622348159937866129)
                  ·
                    refine ⟨446656966761119953399597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595542622348159937866129 446656966761119953399597)
                    ·
                      refine ⟨167496362535419982524849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 446656966761119953399597 167496362535419982524849)
                      ·
                        rfl

theorem cell23_326198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_326198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326198 prefixEnd_326198 := by exact prefixLift 326198
  have htrace : WordTrace (prefixWord ++ tailWord_326198) baseStart_326198 baseEnd_326198 := by
    simpa [prefixWord, tailWord_326198, baseEnd_326198] using wordTrace_append hprefix tailTrace_326198
  have hstable : (prefixWord ++ tailWord_326198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326198).length < 2 ^ (prefixWord ++ tailWord_326198).sum := by decide
  have hdescent : baseEnd_326198 < baseStart_326198 := by decide
  rcases family_descends (prefixWord ++ tailWord_326198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326228 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_326228 : Nat := 118140960795 + 326228 * 2 ^ 59
def prefixEnd_326228 : Nat := 4983230072969 + 3 ^ 40 * 326228 * 2
def baseEnd_326228 : Nat := 167511766955054865149711

theorem tailTrace_326228 : CollatzResearch.WordTrace tailWord_326228 prefixEnd_326228 167511766955054865149711 := by
  unfold tailWord_326228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949256331069573075893669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7932341774759430767858225 5949256331069573075893669)
  ·
    refine ⟨1115485562075544951730063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5949256331069573075893669 1115485562075544951730063)
    ·
      refine ⟨1673228343113317427595095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115485562075544951730063 1673228343113317427595095)
      ·
        refine ⟨2509842514669976141392643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673228343113317427595095 2509842514669976141392643)
        ·
          refine ⟨3764763772004964212088965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509842514669976141392643 3764763772004964212088965)
          ·
            refine ⟨705893207250930789766681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3764763772004964212088965 705893207250930789766681)
            ·
              refine ⟨529419905438198092325011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705893207250930789766681 529419905438198092325011)
              ·
                refine ⟨794129858157297138487517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529419905438198092325011 794129858157297138487517)
                ·
                  refine ⟨297798696808986426932819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 794129858157297138487517 297798696808986426932819)
                  ·
                    refine ⟨446698045213479640399229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 297798696808986426932819 446698045213479640399229)
                    ·
                      refine ⟨167511766955054865149711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 446698045213479640399229 167511766955054865149711)
                      ·
                        rfl

theorem cell23_326228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_326228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326228 prefixEnd_326228 := by exact prefixLift 326228
  have htrace : WordTrace (prefixWord ++ tailWord_326228) baseStart_326228 baseEnd_326228 := by
    simpa [prefixWord, tailWord_326228, baseEnd_326228] using wordTrace_append hprefix tailTrace_326228
  have hstable : (prefixWord ++ tailWord_326228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326228).length < 2 ^ (prefixWord ++ tailWord_326228).sum := by decide
  have hdescent : baseEnd_326228 < baseStart_326228 := by decide
  rcases family_descends (prefixWord ++ tailWord_326228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326248 : List Nat := [2, 1, 4, 3, 2, 1, 2, 2, 1, 5]
def baseStart_326248 : Nat := 118140960795 + 326248 * 2 ^ 59
def prefixEnd_326248 : Nat := 4983230072969 + 3 ^ 40 * 326248 * 2
def baseEnd_326248 : Nat := 55840678856048262299873

theorem tailTrace_326248 : CollatzResearch.WordTrace tailWord_326248 prefixEnd_326248 55840678856048262299873 := by
  unfold tailWord_326248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949621061033344783757699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7932828081377793045010265 5949621061033344783757699)
  ·
    refine ⟨8924431591550017175636549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5949621061033344783757699 8924431591550017175636549)
    ·
      refine ⟨1673330923415628220431853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8924431591550017175636549 1673330923415628220431853)
      ·
        refine ⟨627499096280860582661945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1673330923415628220431853 627499096280860582661945)
        ·
          refine ⟨470624322210645436996459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627499096280860582661945 470624322210645436996459)
          ·
            refine ⟨705936483315968155494689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470624322210645436996459 705936483315968155494689)
            ·
              refine ⟨529452362486976116621017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 705936483315968155494689 529452362486976116621017)
              ·
                refine ⟨397089271865232087465763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529452362486976116621017 397089271865232087465763)
                ·
                  refine ⟨595633907797848131198645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397089271865232087465763 595633907797848131198645)
                  ·
                    refine ⟨55840678856048262299873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 595633907797848131198645 55840678856048262299873)
                    ·
                      rfl

theorem cell23_326248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_326248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326248 prefixEnd_326248 := by exact prefixLift 326248
  have htrace : WordTrace (prefixWord ++ tailWord_326248) baseStart_326248 baseEnd_326248 := by
    simpa [prefixWord, tailWord_326248, baseEnd_326248] using wordTrace_append hprefix tailTrace_326248
  have hstable : (prefixWord ++ tailWord_326248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326248).length < 2 ^ (prefixWord ++ tailWord_326248).sum := by decide
  have hdescent : baseEnd_326248 < baseStart_326248 := by decide
  rcases family_descends (prefixWord ++ tailWord_326248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326251 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 5, 2, 2]
def baseStart_326251 : Nat := 118140960795 + 326251 * 2 ^ 59
def prefixEnd_326251 : Nat := 4983230072969 + 3 ^ 40 * 326251 * 2
def baseEnd_326251 : Nat := 167523577010108275162105

theorem tailTrace_326251 : CollatzResearch.WordTrace tailWord_326251 prefixEnd_326251 167523577010108275162105 := by
  unfold tailWord_326251
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899351541055821079874607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7932901027370547386583071 11899351541055821079874607)
  ·
    refine ⟨17849027311583731619811911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11899351541055821079874607 17849027311583731619811911)
    ·
      refine ⟨26773540967375597429717867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17849027311583731619811911 26773540967375597429717867)
      ·
        refine ⟨40160311451063396144576801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26773540967375597429717867 40160311451063396144576801)
        ·
          refine ⟨30120233588297547108432601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40160311451063396144576801 30120233588297547108432601)
          ·
            refine ⟨22590175191223160331324451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30120233588297547108432601 22590175191223160331324451)
            ·
              refine ⟨33885262786834740496986677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22590175191223160331324451 33885262786834740496986677)
              ·
                refine ⟨3176743386265756921592501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33885262786834740496986677 3176743386265756921592501)
                ·
                  refine ⟨297819692462414711399297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3176743386265756921592501 297819692462414711399297)
                  ·
                    refine ⟨223364769346811033549473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 297819692462414711399297 223364769346811033549473)
                    ·
                      refine ⟨167523577010108275162105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223364769346811033549473 167523577010108275162105)
                      ·
                        rfl

theorem cell23_326251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 2, 2].length) (baseStart_326251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326251 prefixEnd_326251 := by exact prefixLift 326251
  have htrace : WordTrace (prefixWord ++ tailWord_326251) baseStart_326251 baseEnd_326251 := by
    simpa [prefixWord, tailWord_326251, baseEnd_326251] using wordTrace_append hprefix tailTrace_326251
  have hstable : (prefixWord ++ tailWord_326251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326251).length < 2 ^ (prefixWord ++ tailWord_326251).sum := by decide
  have hdescent : baseEnd_326251 < baseStart_326251 := by decide
  rcases family_descends (prefixWord ++ tailWord_326251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326284 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_326284 : Nat := 118140960795 + 326284 * 2 ^ 59
def prefixEnd_326284 : Nat := 4983230072969 + 3 ^ 40 * 326284 * 2
def baseEnd_326284 : Nat := 167540521871706646049453

theorem tailTrace_326284 : CollatzResearch.WordTrace tailWord_326284 prefixEnd_326284 167540521871706646049453 := by
  unfold tailWord_326284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5950277574968133857912953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7933703433290845143883937 5950277574968133857912953)
  ·
    refine ⟨4462708181226100393434715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5950277574968133857912953 4462708181226100393434715)
    ·
      refine ⟨6694062271839150590152073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4462708181226100393434715 6694062271839150590152073)
      ·
        refine ⟨5020546703879362942614055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6694062271839150590152073 5020546703879362942614055)
        ·
          refine ⟨7530820055819044413921083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020546703879362942614055 7530820055819044413921083)
          ·
            refine ⟨11296230083728566620881625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7530820055819044413921083 11296230083728566620881625)
            ·
              refine ⟨8472172562796424965661219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11296230083728566620881625 8472172562796424965661219)
              ·
                refine ⟨12708258844194637448491829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8472172562796424965661219 12708258844194637448491829)
                ·
                  refine ⟨1191399266643247260796109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12708258844194637448491829 1191399266643247260796109)
                  ·
                    refine ⟨446774724991217722798541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191399266643247260796109 446774724991217722798541)
                    ·
                      refine ⟨167540521871706646049453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 446774724991217722798541 167540521871706646049453)
                      ·
                        rfl

theorem cell23_326284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_326284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326284 prefixEnd_326284 := by exact prefixLift 326284
  have htrace : WordTrace (prefixWord ++ tailWord_326284) baseStart_326284 baseEnd_326284 := by
    simpa [prefixWord, tailWord_326284, baseEnd_326284] using wordTrace_append hprefix tailTrace_326284
  have hstable : (prefixWord ++ tailWord_326284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326284).length < 2 ^ (prefixWord ++ tailWord_326284).sum := by decide
  have hdescent : baseEnd_326284 < baseStart_326284 := by decide
  rcases family_descends (prefixWord ++ tailWord_326284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326287 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 1, 9]
def baseStart_326287 : Nat := 118140960795 + 326287 * 2 ^ 59
def prefixEnd_326287 : Nat := 4983230072969 + 3 ^ 40 * 326287 * 2
def baseEnd_326287 : Nat := 55847354104556711437313

theorem tailTrace_326287 : CollatzResearch.WordTrace tailWord_326287 prefixEnd_326287 55847354104556711437313 := by
  unfold tailWord_326287
  simp only [CollatzResearch.WordTrace]
  refine ⟨11900664568925399228185115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7933776379283599485456743 11900664568925399228185115)
  ·
    refine ⟨17850996853388098842277673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11900664568925399228185115 17850996853388098842277673)
    ·
      refine ⟨13388247640041074131708255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17850996853388098842277673 13388247640041074131708255)
      ·
        refine ⟨20082371460061611197562383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13388247640041074131708255 20082371460061611197562383)
        ·
          refine ⟨30123557190092416796343575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20082371460061611197562383 30123557190092416796343575)
          ·
            refine ⟨45185335785138625194515363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30123557190092416796343575 45185335785138625194515363)
            ·
              refine ⟨67778003677707937791773045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45185335785138625194515363 67778003677707937791773045)
              ·
                refine ⟨6354187844785119167978723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67778003677707937791773045 6354187844785119167978723)
                ·
                  refine ⟨9531281767177678751968085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6354187844785119167978723 9531281767177678751968085)
                  ·
                    refine ⟨55847354104556711437313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9531281767177678751968085 55847354104556711437313)
                    ·
                      rfl

theorem cell23_326287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_326287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326287 prefixEnd_326287 := by exact prefixLift 326287
  have htrace : WordTrace (prefixWord ++ tailWord_326287) baseStart_326287 baseEnd_326287 := by
    simpa [prefixWord, tailWord_326287, baseEnd_326287] using wordTrace_append hprefix tailTrace_326287
  have hstable : (prefixWord ++ tailWord_326287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326287).length < 2 ^ (prefixWord ++ tailWord_326287).sum := by decide
  have hdescent : baseEnd_326287 < baseStart_326287 := by decide
  rcases family_descends (prefixWord ++ tailWord_326287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326305 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_326305 : Nat := 118140960795 + 326305 * 2 ^ 59
def prefixEnd_326305 : Nat := 4983230072969 + 3 ^ 40 * 326305 * 2
def baseEnd_326305 : Nat := 167551304965451063886857

theorem tailTrace_326305 : CollatzResearch.WordTrace tailWord_326305 prefixEnd_326305 167551304965451063886857 := by
  unfold tailWord_326305
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901321082860188302340369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7934214055240125534893579 11901321082860188302340369)
  ·
    refine ⟨8925990812145141226755277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11901321082860188302340369 8925990812145141226755277)
    ·
      refine ⟨3347246554554427960033229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8925990812145141226755277 3347246554554427960033229)
      ·
        refine ⟨1255217457957910485012461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3347246554554427960033229 1255217457957910485012461)
        ·
          refine ⟨470706546734216431879673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1255217457957910485012461 470706546734216431879673)
          ·
            refine ⟨353029910050662323909755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470706546734216431879673 353029910050662323909755)
            ·
              refine ⟨529544865075993485864633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353029910050662323909755 529544865075993485864633)
              ·
                refine ⟨397158648806995114398475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 529544865075993485864633 397158648806995114398475)
                ·
                  refine ⟨595737973210492671597713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397158648806995114398475 595737973210492671597713)
                  ·
                    refine ⟨446803479907869503698285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 595737973210492671597713 446803479907869503698285)
                    ·
                      refine ⟨167551304965451063886857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 446803479907869503698285 167551304965451063886857)
                      ·
                        rfl

theorem cell23_326305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_326305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326305 prefixEnd_326305 := by exact prefixLift 326305
  have htrace : WordTrace (prefixWord ++ tailWord_326305) baseStart_326305 baseEnd_326305 := by
    simpa [prefixWord, tailWord_326305, baseEnd_326305] using wordTrace_append hprefix tailTrace_326305
  have hstable : (prefixWord ++ tailWord_326305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326305).length < 2 ^ (prefixWord ++ tailWord_326305).sum := by decide
  have hdescent : baseEnd_326305 < baseStart_326305 := by decide
  rcases family_descends (prefixWord ++ tailWord_326305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326318 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_326318 : Nat := 118140960795 + 326318 * 2 ^ 59
def prefixEnd_326318 : Nat := 4983230072969 + 3 ^ 40 * 326318 * 2
def baseEnd_326318 : Nat := 167557980213959513024297

theorem tailTrace_326318 : CollatzResearch.WordTrace tailWord_326318 prefixEnd_326318 167557980213959513024297 := by
  unfold tailWord_326318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487724403976636440320451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7934530154542061015042405 1487724403976636440320451)
  ·
    refine ⟨2231586605964954660480677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1487724403976636440320451 2231586605964954660480677)
    ·
      refine ⟨418422488618428998840127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2231586605964954660480677 418422488618428998840127)
      ·
        refine ⟨627633732927643498260191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418422488618428998840127 627633732927643498260191)
        ·
          refine ⟨941450599391465247390287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627633732927643498260191 941450599391465247390287)
          ·
            refine ⟨1412175899087197871085431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941450599391465247390287 1412175899087197871085431)
            ·
              refine ⟨2118263848630796806628147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1412175899087197871085431 2118263848630796806628147)
              ·
                refine ⟨3177395772946195209942221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118263848630796806628147 3177395772946195209942221)
                ·
                  refine ⟨1191523414854823203728333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3177395772946195209942221 1191523414854823203728333)
                  ·
                    refine ⟨446821280570558701398125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191523414854823203728333 446821280570558701398125)
                    ·
                      refine ⟨167557980213959513024297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 446821280570558701398125 167557980213959513024297)
                      ·
                        rfl

theorem cell23_326318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_326318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326318 prefixEnd_326318 := by exact prefixLift 326318
  have htrace : WordTrace (prefixWord ++ tailWord_326318) baseStart_326318 baseEnd_326318 := by
    simpa [prefixWord, tailWord_326318, baseEnd_326318] using wordTrace_append hprefix tailTrace_326318
  have hstable : (prefixWord ++ tailWord_326318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326318).length < 2 ^ (prefixWord ++ tailWord_326318).sum := by decide
  have hdescent : baseEnd_326318 < baseStart_326318 := by decide
  rcases family_descends (prefixWord ++ tailWord_326318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326342 : List Nat := [6, 1, 2, 1, 3, 1, 1, 8]
def baseStart_326342 : Nat := 118140960795 + 326342 * 2 ^ 59
def prefixEnd_326342 : Nat := 4983230072969 + 3 ^ 40 * 326342 * 2
def baseEnd_326342 : Nat := 6206307546283978486081

theorem tailTrace_326342 : CollatzResearch.WordTrace tailWord_326342 prefixEnd_326342 6206307546283978486081 := by
  unfold tailWord_326342
  simp only [CollatzResearch.WordTrace]
  refine ⟨371958455741441988169915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7935113722484095747624853 371958455741441988169915)
  ·
    refine ⟨557937683612162982254873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371958455741441988169915 557937683612162982254873)
    ·
      refine ⟨418453262709122236691155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 557937683612162982254873 418453262709122236691155)
      ·
        refine ⟨627679894063683355036733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418453262709122236691155 627679894063683355036733)
        ·
          refine ⟨235379960273881258138775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627679894063683355036733 235379960273881258138775)
          ·
            refine ⟨353069940410821887208163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235379960273881258138775 353069940410821887208163)
            ·
              refine ⟨529604910616232830812245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353069940410821887208163 529604910616232830812245)
              ·
                refine ⟨6206307546283978486081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 529604910616232830812245 6206307546283978486081)
                ·
                  rfl

theorem cell23_326342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_326342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326342 prefixEnd_326342 := by exact prefixLift 326342
  have htrace : WordTrace (prefixWord ++ tailWord_326342) baseStart_326342 baseEnd_326342 := by
    simpa [prefixWord, tailWord_326342, baseEnd_326342] using wordTrace_append hprefix tailTrace_326342
  have hstable : (prefixWord ++ tailWord_326342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326342).length < 2 ^ (prefixWord ++ tailWord_326342).sum := by decide
  have hdescent : baseEnd_326342 < baseStart_326342 := by decide
  rcases family_descends (prefixWord ++ tailWord_326342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326398 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 7]
def baseStart_326398 : Nat := 118140960795 + 326398 * 2 ^ 59
def prefixEnd_326398 : Nat := 4983230072969 + 3 ^ 40 * 326398 * 2
def baseEnd_326398 : Nat := 18622117629591022224881

theorem tailTrace_326398 : CollatzResearch.WordTrace tailWord_326398 prefixEnd_326398 18622117629591022224881 := by
  unfold tailWord_326398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488089133940408148184481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7936475381015510123650565 1488089133940408148184481)
  ·
    refine ⟨1116066850455306111138361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1488089133940408148184481 1116066850455306111138361)
    ·
      refine ⟨837050137841479583353771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116066850455306111138361 837050137841479583353771)
      ·
        refine ⟨1255575206762219375030657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837050137841479583353771 1255575206762219375030657)
        ·
          refine ⟨941681405071664531272993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1255575206762219375030657 941681405071664531272993)
          ·
            refine ⟨706261053803748398454745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 941681405071664531272993 706261053803748398454745)
            ·
              refine ⟨529695790352811298841059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706261053803748398454745 529695790352811298841059)
              ·
                refine ⟨794543685529216948261589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529695790352811298841059 794543685529216948261589)
                ·
                  refine ⟨18622117629591022224881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 794543685529216948261589 18622117629591022224881)
                  ·
                    rfl

theorem cell23_326398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_326398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326398 prefixEnd_326398 := by exact prefixLift 326398
  have htrace : WordTrace (prefixWord ++ tailWord_326398) baseStart_326398 baseEnd_326398 := by
    simpa [prefixWord, tailWord_326398, baseEnd_326398] using wordTrace_append hprefix tailTrace_326398
  have hstable : (prefixWord ++ tailWord_326398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326398).length < 2 ^ (prefixWord ++ tailWord_326398).sum := by decide
  have hdescent : baseEnd_326398 < baseStart_326398 := by decide
  rcases family_descends (prefixWord ++ tailWord_326398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326424 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 1, 10]
def baseStart_326424 : Nat := 118140960795 + 326424 * 2 ^ 59
def prefixEnd_326424 : Nat := 4983230072969 + 3 ^ 40 * 326424 * 2
def baseEnd_326424 : Nat := 55870803054445366099603

theorem tailTrace_326424 : CollatzResearch.WordTrace tailWord_326424 prefixEnd_326424 55870803054445366099603 := by
  unfold tailWord_326424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952830684714535812961163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7937107579619381083948217 5952830684714535812961163)
  ·
    refine ⟨8929246027071803719441745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5952830684714535812961163 8929246027071803719441745)
    ·
      refine ⟨6696934520303852789581309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8929246027071803719441745 6696934520303852789581309)
      ·
        refine ⟨2511350445113944796092991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6696934520303852789581309 2511350445113944796092991)
        ·
          refine ⟨3767025667670917194139487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511350445113944796092991 3767025667670917194139487)
          ·
            refine ⟨5650538501506375791209231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767025667670917194139487 5650538501506375791209231)
            ·
              refine ⟨8475807752259563686813847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5650538501506375791209231 8475807752259563686813847)
              ·
                refine ⟨12713711628389345530220771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8475807752259563686813847 12713711628389345530220771)
                ·
                  refine ⟨19070567442584018295331157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12713711628389345530220771 19070567442584018295331157)
                  ·
                    refine ⟨55870803054445366099603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 19070567442584018295331157 55870803054445366099603)
                    ·
                      rfl

theorem cell23_326424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_326424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326424 prefixEnd_326424 := by exact prefixLift 326424
  have htrace : WordTrace (prefixWord ++ tailWord_326424) baseStart_326424 baseEnd_326424 := by
    simpa [prefixWord, tailWord_326424, baseEnd_326424] using wordTrace_append hprefix tailTrace_326424
  have hstable : (prefixWord ++ tailWord_326424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326424).length < 2 ^ (prefixWord ++ tailWord_326424).sum := by decide
  have hdescent : baseEnd_326424 < baseStart_326424 := by decide
  rcases family_descends (prefixWord ++ tailWord_326424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326431 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_326431 : Nat := 118140960795 + 326431 * 2 ^ 59
def prefixEnd_326431 : Nat := 4983230072969 + 3 ^ 40 * 326431 * 2
def baseEnd_326431 : Nat := 167616003527917570911277

theorem tailTrace_326431 : CollatzResearch.WordTrace tailWord_326431 prefixEnd_326431 167616003527917570911277 := by
  unfold tailWord_326431
  simp only [CollatzResearch.WordTrace]
  refine ⟨11905916680403711821427147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7937277786935807880951431 11905916680403711821427147)
  ·
    refine ⟨17858875020605567732140721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11905916680403711821427147 17858875020605567732140721)
    ·
      refine ⟨13394156265454175799105541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17858875020605567732140721 13394156265454175799105541)
      ·
        refine ⟨2511404299772657962332289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13394156265454175799105541 2511404299772657962332289)
        ·
          refine ⟨1883553224829493471749217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511404299772657962332289 1883553224829493471749217)
          ·
            refine ⟨1412664918622120103811913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883553224829493471749217 1412664918622120103811913)
            ·
              refine ⟨1059498688966590077858935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412664918622120103811913 1059498688966590077858935)
              ·
                refine ⟨1589248033449885116788403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059498688966590077858935 1589248033449885116788403)
                ·
                  refine ⟨2383872050174827675182605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589248033449885116788403 2383872050174827675182605)
                  ·
                    refine ⟨893952018815560378193477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383872050174827675182605 893952018815560378193477)
                    ·
                      refine ⟨167616003527917570911277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 893952018815560378193477 167616003527917570911277)
                      ·
                        rfl

theorem cell23_326431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_326431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326431 prefixEnd_326431 := by exact prefixLift 326431
  have htrace : WordTrace (prefixWord ++ tailWord_326431) baseStart_326431 baseEnd_326431 := by
    simpa [prefixWord, tailWord_326431, baseEnd_326431] using wordTrace_append hprefix tailTrace_326431
  have hstable : (prefixWord ++ tailWord_326431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326431).length < 2 ^ (prefixWord ++ tailWord_326431).sum := by decide
  have hdescent : baseEnd_326431 < baseStart_326431 := by decide
  rcases family_descends (prefixWord ++ tailWord_326431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326548 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_326548 : Nat := 118140960795 + 326548 * 2 ^ 59
def prefixEnd_326548 : Nat := 4983230072969 + 3 ^ 40 * 326548 * 2
def baseEnd_326548 : Nat := 55892026921497871049413

theorem tailTrace_326548 : CollatzResearch.WordTrace tailWord_326548 prefixEnd_326548 55892026921497871049413 := by
  unfold tailWord_326548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5955092010489920401718149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7940122680653227202290865 5955092010489920401718149)
  ·
    refine ⟨1116579751966860075322153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5955092010489920401718149 1116579751966860075322153)
    ·
      refine ⟨837434813975145056491615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116579751966860075322153 837434813975145056491615)
      ·
        refine ⟨1256152220962717584737423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837434813975145056491615 1256152220962717584737423)
        ·
          refine ⟨1884228331444076377106135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1256152220962717584737423 1884228331444076377106135)
          ·
            refine ⟨2826342497166114565659203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884228331444076377106135 2826342497166114565659203)
            ·
              refine ⟨4239513745749171848488805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826342497166114565659203 4239513745749171848488805)
              ·
                refine ⟨794908827327969721591651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4239513745749171848488805 794908827327969721591651)
                ·
                  refine ⟨1192363240991954582387477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794908827327969721591651 1192363240991954582387477)
                  ·
                    refine ⟨55892026921497871049413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1192363240991954582387477 55892026921497871049413)
                    ·
                      rfl

theorem cell23_326548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_326548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326548 prefixEnd_326548 := by exact prefixLift 326548
  have htrace : WordTrace (prefixWord ++ tailWord_326548) baseStart_326548 baseEnd_326548 := by
    simpa [prefixWord, tailWord_326548, baseEnd_326548] using wordTrace_append hprefix tailTrace_326548
  have hstable : (prefixWord ++ tailWord_326548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326548).length < 2 ^ (prefixWord ++ tailWord_326548).sum := by decide
  have hdescent : baseEnd_326548 < baseStart_326548 := by decide
  rcases family_descends (prefixWord ++ tailWord_326548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326585 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 4]
def baseStart_326585 : Nat := 118140960795 + 326585 * 2 ^ 59
def prefixEnd_326585 : Nat := 4983230072969 + 3 ^ 40 * 326585 * 2
def baseEnd_326585 : Nat := 167695079548709968385569

theorem tailTrace_326585 : CollatzResearch.WordTrace tailWord_326585 prefixEnd_326585 167695079548709968385569 := by
  unfold tailWord_326585
  simp only [CollatzResearch.WordTrace]
  refine ⟨11911533521845796122533209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7941022347897197415022139 11911533521845796122533209)
  ·
    refine ⟨8933650141384347091899907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11911533521845796122533209 8933650141384347091899907)
    ·
      refine ⟨13400475212076520637849861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933650141384347091899907 13400475212076520637849861)
      ·
        refine ⟨2512589102264347619596849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13400475212076520637849861 2512589102264347619596849)
        ·
          refine ⟨1884441826698260714697637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2512589102264347619596849 1884441826698260714697637)
          ·
            refine ⟨353332842505923884005807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1884441826698260714697637 353332842505923884005807)
            ·
              refine ⟨529999263758885826008711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353332842505923884005807 529999263758885826008711)
              ·
                refine ⟨794998895638328739013067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529999263758885826008711 794998895638328739013067)
                ·
                  refine ⟨1192498343457493108519601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794998895638328739013067 1192498343457493108519601)
                  ·
                    refine ⟨894373757593119831389701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1192498343457493108519601 894373757593119831389701)
                    ·
                      refine ⟨167695079548709968385569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 894373757593119831389701 167695079548709968385569)
                      ·
                        rfl

theorem cell23_326585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_326585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326585 prefixEnd_326585 := by exact prefixLift 326585
  have htrace : WordTrace (prefixWord ++ tailWord_326585) baseStart_326585 baseEnd_326585 := by
    simpa [prefixWord, tailWord_326585, baseEnd_326585] using wordTrace_append hprefix tailTrace_326585
  have hstable : (prefixWord ++ tailWord_326585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326585).length < 2 ^ (prefixWord ++ tailWord_326585).sum := by decide
  have hdescent : baseEnd_326585 < baseStart_326585 := by decide
  rcases family_descends (prefixWord ++ tailWord_326585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326606 : List Nat := [4, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_326606 : Nat := 118140960795 + 326606 * 2 ^ 59
def prefixEnd_326606 : Nat := 4983230072969 + 3 ^ 40 * 326606 * 2
def baseEnd_326606 : Nat := 167705862642454386222973

theorem tailTrace_326606 : CollatzResearch.WordTrace tailWord_326606 prefixEnd_326606 167705862642454386222973 := by
  unfold tailWord_326606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489037431846214588630959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7941532969846477806031781 1489037431846214588630959)
  ·
    refine ⟨2233556147769321882946439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1489037431846214588630959 2233556147769321882946439)
    ·
      refine ⟨3350334221653982824419659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233556147769321882946439 3350334221653982824419659)
      ·
        refine ⟨5025501332480974236629489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3350334221653982824419659 5025501332480974236629489)
        ·
          refine ⟨3769125999360730677472117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5025501332480974236629489 3769125999360730677472117)
          ·
            refine ⟨353355562440068501013011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3769125999360730677472117 353355562440068501013011)
            ·
              refine ⟨530033343660102751519517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353355562440068501013011 530033343660102751519517)
              ·
                refine ⟨198762503872538531819819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530033343660102751519517 198762503872538531819819)
                ·
                  refine ⟨298143755808807797729729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198762503872538531819819 298143755808807797729729)
                  ·
                    refine ⟨223607816856605848297297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 298143755808807797729729 223607816856605848297297)
                    ·
                      refine ⟨167705862642454386222973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223607816856605848297297 167705862642454386222973)
                      ·
                        rfl

theorem cell23_326606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_326606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326606 prefixEnd_326606 := by exact prefixLift 326606
  have htrace : WordTrace (prefixWord ++ tailWord_326606) baseStart_326606 baseEnd_326606 := by
    simpa [prefixWord, tailWord_326606, baseEnd_326606] using wordTrace_append hprefix tailTrace_326606
  have hstable : (prefixWord ++ tailWord_326606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326606).length < 2 ^ (prefixWord ++ tailWord_326606).sum := by decide
  have hdescent : baseEnd_326606 < baseStart_326606 := by decide
  rcases family_descends (prefixWord ++ tailWord_326606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326639 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 2, 1, 3]
def baseStart_326639 : Nat := 118140960795 + 326639 * 2 ^ 59
def prefixEnd_326639 : Nat := 4983230072969 + 3 ^ 40 * 326639 * 2
def baseEnd_326639 : Nat := 167722807504052757110321

theorem tailTrace_326639 : CollatzResearch.WordTrace tailWord_326639 prefixEnd_326639 167722807504052757110321 := by
  unfold tailWord_326639
  simp only [CollatzResearch.WordTrace]
  refine ⟨11913503063650163344998971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7942335375766775563332647 11913503063650163344998971)
  ·
    refine ⟨17870254595475245017498457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11913503063650163344998971 17870254595475245017498457)
    ·
      refine ⟨13402690946606433763123843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17870254595475245017498457 13402690946606433763123843)
      ·
        refine ⟨20104036419909650644685765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13402690946606433763123843 20104036419909650644685765)
        ·
          refine ⟨3769506828733059495878581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20104036419909650644685765 3769506828733059495878581)
          ·
            refine ⟨353391265193724327738617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3769506828733059495878581 353391265193724327738617)
            ·
              refine ⟨265043448895293245803963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353391265193724327738617 265043448895293245803963)
              ·
                refine ⟨397565173342939868705945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265043448895293245803963 397565173342939868705945)
                ·
                  refine ⟨298173880007204901529459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397565173342939868705945 298173880007204901529459)
                  ·
                    refine ⟨447260820010807352294189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 298173880007204901529459 447260820010807352294189)
                    ·
                      refine ⟨167722807504052757110321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 447260820010807352294189 167722807504052757110321)
                      ·
                        rfl

theorem cell23_326639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 2, 1, 3].length) (baseStart_326639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326639 prefixEnd_326639 := by exact prefixLift 326639
  have htrace : WordTrace (prefixWord ++ tailWord_326639) baseStart_326639 baseEnd_326639 := by
    simpa [prefixWord, tailWord_326639, baseEnd_326639] using wordTrace_append hprefix tailTrace_326639
  have hstable : (prefixWord ++ tailWord_326639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326639).length < 2 ^ (prefixWord ++ tailWord_326639).sum := by decide
  have hdescent : baseEnd_326639 < baseStart_326639 := by decide
  rcases family_descends (prefixWord ++ tailWord_326639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326651 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 9]
def baseStart_326651 : Nat := 118140960795 + 326651 * 2 ^ 59
def prefixEnd_326651 : Nat := 4983230072969 + 3 ^ 40 * 326651 * 2
def baseEnd_326651 : Nat := 18636552141322967795585

theorem tailTrace_326651 : CollatzResearch.WordTrace tailWord_326651 prefixEnd_326651 18636552141322967795585 := by
  unfold tailWord_326651
  simp only [CollatzResearch.WordTrace]
  refine ⟨11913940739606689394435807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7942627159737792929623871 11913940739606689394435807)
  ·
    refine ⟨17870911109410034091653711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11913940739606689394435807 17870911109410034091653711)
    ·
      refine ⟨26806366664115051137480567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17870911109410034091653711 26806366664115051137480567)
      ·
        refine ⟨40209549996172576706220851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26806366664115051137480567 40209549996172576706220851)
        ·
          refine ⟨60314324994258865059331277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40209549996172576706220851 60314324994258865059331277)
          ·
            refine ⟨22617871872847074397249229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60314324994258865059331277 22617871872847074397249229)
            ·
              refine ⟨8481701952317652898968461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22617871872847074397249229 8481701952317652898968461)
              ·
                refine ⟨3180638232119119837113173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8481701952317652898968461 3180638232119119837113173)
                ·
                  refine ⟨18636552141322967795585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3180638232119119837113173 18636552141322967795585)
                  ·
                    rfl

theorem cell23_326651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 9].length) (baseStart_326651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326651 prefixEnd_326651 := by exact prefixLift 326651
  have htrace : WordTrace (prefixWord ++ tailWord_326651) baseStart_326651 baseEnd_326651 := by
    simpa [prefixWord, tailWord_326651, baseEnd_326651] using wordTrace_append hprefix tailTrace_326651
  have hstable : (prefixWord ++ tailWord_326651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326651).length < 2 ^ (prefixWord ++ tailWord_326651).sum := by decide
  have hdescent : baseEnd_326651 < baseStart_326651 := by decide
  rcases family_descends (prefixWord ++ tailWord_326651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326674 : List Nat := [3, 2, 5, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_326674 : Nat := 118140960795 + 326674 * 2 ^ 59
def prefixEnd_326674 : Nat := 4983230072969 + 3 ^ 40 * 326674 * 2
def baseEnd_326674 : Nat := 167740779326960120172661

theorem tailTrace_326674 : CollatzResearch.WordTrace tailWord_326674 prefixEnd_326674 167740779326960120172661 := by
  unfold tailWord_326674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978694904630841080630769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7943186412348909548348717 2978694904630841080630769)
  ·
    refine ⟨2234021178473130810473077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2978694904630841080630769 2234021178473130810473077)
    ·
      refine ⟨209439485481856013481851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2234021178473130810473077 209439485481856013481851)
      ·
        refine ⟨314159228222784020222777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209439485481856013481851 314159228222784020222777)
        ·
          refine ⟨235619421167088015167083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314159228222784020222777 235619421167088015167083)
          ·
            refine ⟨353429131750632022750625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235619421167088015167083 353429131750632022750625)
            ·
              refine ⟨265071848812974017062969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353429131750632022750625 265071848812974017062969)
              ·
                refine ⟨198803886609730512797227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265071848812974017062969 198803886609730512797227)
                ·
                  refine ⟨298205829914595769195841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198803886609730512797227 298205829914595769195841)
                  ·
                    refine ⟨223654372435946826896881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 298205829914595769195841 223654372435946826896881)
                    ·
                      refine ⟨167740779326960120172661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223654372435946826896881 167740779326960120172661)
                      ·
                        rfl

theorem cell23_326674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_326674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326674 prefixEnd_326674 := by exact prefixLift 326674
  have htrace : WordTrace (prefixWord ++ tailWord_326674) baseStart_326674 baseEnd_326674 := by
    simpa [prefixWord, tailWord_326674, baseEnd_326674] using wordTrace_append hprefix tailTrace_326674
  have hstable : (prefixWord ++ tailWord_326674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326674).length < 2 ^ (prefixWord ++ tailWord_326674).sum := by decide
  have hdescent : baseEnd_326674 < baseStart_326674 := by decide
  rcases family_descends (prefixWord ++ tailWord_326674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326679 : List Nat := [1, 1, 3, 5, 1, 1, 1, 4, 2, 2, 2]
def baseStart_326679 : Nat := 118140960795 + 326679 * 2 ^ 59
def prefixEnd_326679 : Nat := 4983230072969 + 3 ^ 40 * 326679 * 2
def baseEnd_326679 : Nat := 167743346730232600610137

theorem tailTrace_326679 : CollatzResearch.WordTrace tailWord_326679 prefixEnd_326679 167743346730232600610137 := by
  unfold tailWord_326679
  simp only [CollatzResearch.WordTrace]
  refine ⟨11914961983505250176455091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7943307989003500117636727 11914961983505250176455091)
  ·
    refine ⟨17872442975257875264682637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11914961983505250176455091 17872442975257875264682637)
    ·
      refine ⟨6702166115721703224255989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17872442975257875264682637 6702166115721703224255989)
      ·
        refine ⟨628328073348909677273999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6702166115721703224255989 628328073348909677273999)
        ·
          refine ⟨942492110023364515910999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628328073348909677273999 942492110023364515910999)
          ·
            refine ⟨1413738165035046773866499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942492110023364515910999 1413738165035046773866499)
            ·
              refine ⟨2120607247552570160799749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1413738165035046773866499 2120607247552570160799749)
              ·
                refine ⟨397613858916106905149953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2120607247552570160799749 397613858916106905149953)
                ·
                  refine ⟨298210394187080178862465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397613858916106905149953 298210394187080178862465)
                  ·
                    refine ⟨223657795640310134146849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 298210394187080178862465 223657795640310134146849)
                    ·
                      refine ⟨167743346730232600610137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223657795640310134146849 167743346730232600610137)
                      ·
                        rfl

theorem cell23_326679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_326679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326679 prefixEnd_326679 := by exact prefixLift 326679
  have htrace : WordTrace (prefixWord ++ tailWord_326679) baseStart_326679 baseEnd_326679 := by
    simpa [prefixWord, tailWord_326679, baseEnd_326679] using wordTrace_append hprefix tailTrace_326679
  have hstable : (prefixWord ++ tailWord_326679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326679).length < 2 ^ (prefixWord ++ tailWord_326679).sum := by decide
  have hdescent : baseEnd_326679 < baseStart_326679 := by decide
  rcases family_descends (prefixWord ++ tailWord_326679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326705 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 2, 5, 2]
def baseStart_326705 : Nat := 118140960795 + 326705 * 2 ^ 59
def prefixEnd_326705 : Nat := 4983230072969 + 3 ^ 40 * 326705 * 2
def baseEnd_326705 : Nat := 167756697227249498885017

theorem tailTrace_326705 : CollatzResearch.WordTrace tailWord_326705 prefixEnd_326705 167756697227249498885017 := by
  unfold tailWord_326705
  simp only [CollatzResearch.WordTrace]
  refine ⟨11915910281411056616901569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7943940187607371077934379 11915910281411056616901569)
  ·
    refine ⟨8936932711058292462676177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11915910281411056616901569 8936932711058292462676177)
    ·
      refine ⟨6702699533293719347007133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8936932711058292462676177 6702699533293719347007133)
      ·
        refine ⟨2513512324985144755127675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6702699533293719347007133 2513512324985144755127675)
        ·
          refine ⟨3770268487477717132691513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2513512324985144755127675 3770268487477717132691513)
          ·
            refine ⟨2827701365608287849518635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3770268487477717132691513 2827701365608287849518635)
            ·
              refine ⟨4241552048412431774277953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827701365608287849518635 4241552048412431774277953)
              ·
                refine ⟨3181164036309323830708465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4241552048412431774277953 3181164036309323830708465)
                ·
                  refine ⟨2385873027231992873031349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3181164036309323830708465 2385873027231992873031349)
                  ·
                    refine ⟨223675596302999331846689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2385873027231992873031349 223675596302999331846689)
                    ·
                      refine ⟨167756697227249498885017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223675596302999331846689 167756697227249498885017)
                      ·
                        rfl

theorem cell23_326705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_326705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326705 prefixEnd_326705 := by exact prefixLift 326705
  have htrace : WordTrace (prefixWord ++ tailWord_326705) baseStart_326705 baseEnd_326705 := by
    simpa [prefixWord, tailWord_326705, baseEnd_326705] using wordTrace_append hprefix tailTrace_326705
  have hstable : (prefixWord ++ tailWord_326705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326705).length < 2 ^ (prefixWord ++ tailWord_326705).sum := by decide
  have hdescent : baseEnd_326705 < baseStart_326705 := by decide
  rcases family_descends (prefixWord ++ tailWord_326705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326762 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_326762 : Nat := 118140960795 + 326762 * 2 ^ 59
def prefixEnd_326762 : Nat := 4983230072969 + 3 ^ 40 * 326762 * 2
def baseEnd_326762 : Nat := 55928655208185258624085

theorem tailTrace_326762 : CollatzResearch.WordTrace tailWord_326762 prefixEnd_326762 55928655208185258624085 := by
  unfold tailWord_326762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979497310551138837931635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7945326161469703567817693 2979497310551138837931635)
  ·
    refine ⟨4469245965826708256897453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2979497310551138837931635 4469245965826708256897453)
    ·
      refine ⟨1675967237185015596336545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4469245965826708256897453 1675967237185015596336545)
      ·
        refine ⟨1256975427888761697252409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1675967237185015596336545 1256975427888761697252409)
        ·
          refine ⟨942731570916571272939307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1256975427888761697252409 942731570916571272939307)
          ·
            refine ⟨1414097356374856909408961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 942731570916571272939307 1414097356374856909408961)
            ·
              refine ⟨1060573017281142682056721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414097356374856909408961 1060573017281142682056721)
              ·
                refine ⟨795429762960857011542541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060573017281142682056721 795429762960857011542541)
                ·
                  refine ⟨298286161110321379328453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 795429762960857011542541 298286161110321379328453)
                  ·
                    refine ⟨55928655208185258624085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298286161110321379328453 55928655208185258624085)
                    ·
                      rfl

theorem cell23_326762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_326762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326762 prefixEnd_326762 := by exact prefixLift 326762
  have htrace : WordTrace (prefixWord ++ tailWord_326762) baseStart_326762 baseEnd_326762 := by
    simpa [prefixWord, tailWord_326762, baseEnd_326762] using wordTrace_append hprefix tailTrace_326762
  have hstable : (prefixWord ++ tailWord_326762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326762).length < 2 ^ (prefixWord ++ tailWord_326762).sum := by decide
  have hdescent : baseEnd_326762 < baseStart_326762 := by decide
  rcases family_descends (prefixWord ++ tailWord_326762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326835 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 6, 4]
def baseStart_326835 : Nat := 118140960795 + 326835 * 2 ^ 59
def prefixEnd_326835 : Nat := 4983230072969 + 3 ^ 40 * 326835 * 2
def baseEnd_326835 : Nat := 55941149904111330086473

theorem tailTrace_326835 : CollatzResearch.WordTrace tailWord_326835 prefixEnd_326835 55941149904111330086473 := by
  unfold tailWord_326835
  simp only [CollatzResearch.WordTrace]
  refine ⟨11920651770940088819133959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7947101180626725879422639 11920651770940088819133959)
  ·
    refine ⟨17880977656410133228700939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11920651770940088819133959 17880977656410133228700939)
    ·
      refine ⟨26821466484615199843051409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17880977656410133228700939 26821466484615199843051409)
      ·
        refine ⟨20116099863461399882288557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26821466484615199843051409 20116099863461399882288557)
        ·
          refine ⟨7543537448798024955858209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20116099863461399882288557 7543537448798024955858209)
          ·
            refine ⟨5657653086598518716893657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7543537448798024955858209 5657653086598518716893657)
            ·
              refine ⟨4243239814948889037670243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5657653086598518716893657 4243239814948889037670243)
              ·
                refine ⟨6364859722423333556505365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4243239814948889037670243 6364859722423333556505365)
                ·
                  refine ⟨298352799488593760461189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6364859722423333556505365 298352799488593760461189)
                  ·
                    refine ⟨55941149904111330086473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298352799488593760461189 55941149904111330086473)
                    ·
                      rfl

theorem cell23_326835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 4].length) (baseStart_326835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326835 prefixEnd_326835 := by exact prefixLift 326835
  have htrace : WordTrace (prefixWord ++ tailWord_326835) baseStart_326835 baseEnd_326835 := by
    simpa [prefixWord, tailWord_326835, baseEnd_326835] using wordTrace_append hprefix tailTrace_326835
  have hstable : (prefixWord ++ tailWord_326835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326835).length < 2 ^ (prefixWord ++ tailWord_326835).sum := by decide
  have hdescent : baseEnd_326835 < baseStart_326835 := by decide
  rcases family_descends (prefixWord ++ tailWord_326835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326848 : List Nat := [2, 1, 1, 2, 17]
def baseStart_326848 : Nat := 118140960795 + 326848 * 2 ^ 59
def prefixEnd_326848 : Nat := 4983230072969 + 3 ^ 40 * 326848 * 2
def baseEnd_326848 : Nat := 230219650152047241971

theorem tailTrace_326848 : CollatzResearch.WordTrace tailWord_326848 prefixEnd_326848 230219650152047241971 := by
  unfold tailWord_326848
  simp only [CollatzResearch.WordTrace]
  refine ⟨5960562959946496019678599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7947417279928661359571465 5960562959946496019678599)
  ·
    refine ⟨8940844439919744029517899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5960562959946496019678599 8940844439919744029517899)
    ·
      refine ⟨13411266659879616044276849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8940844439919744029517899 13411266659879616044276849)
      ·
        refine ⟨10058449994909712033207637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13411266659879616044276849 10058449994909712033207637)
        ·
          refine ⟨230219650152047241971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 17 10058449994909712033207637 230219650152047241971)
          ·
            rfl

theorem cell23_326848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 17].length) (baseStart_326848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326848 prefixEnd_326848 := by exact prefixLift 326848
  have htrace : WordTrace (prefixWord ++ tailWord_326848) baseStart_326848 baseEnd_326848 := by
    simpa [prefixWord, tailWord_326848, baseEnd_326848] using wordTrace_append hprefix tailTrace_326848
  have hstable : (prefixWord ++ tailWord_326848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326848).length < 2 ^ (prefixWord ++ tailWord_326848).sum := by decide
  have hdescent : baseEnd_326848 < baseStart_326848 := by decide
  rcases family_descends (prefixWord ++ tailWord_326848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326869 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_326869 : Nat := 118140960795 + 326869 * 2 ^ 59
def prefixEnd_326869 : Nat := 4983230072969 + 3 ^ 40 * 326869 * 2
def baseEnd_326869 : Nat := 55946969351528952411421

theorem tailTrace_326869 : CollatzResearch.WordTrace tailWord_326869 prefixEnd_326869 55946969351528952411421 := by
  unfold tailWord_326869
  simp only [CollatzResearch.WordTrace]
  refine ⟨11921891852816912625871661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7947927901877941750581107 11921891852816912625871661)
  ·
    refine ⟨4470709444806342234701873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11921891852816912625871661 4470709444806342234701873)
    ·
      refine ⟨3353032083604756676026405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4470709444806342234701873 3353032083604756676026405)
      ·
        refine ⟨628693515675891876754951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3353032083604756676026405 628693515675891876754951)
        ·
          refine ⟨943040273513837815132427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628693515675891876754951 943040273513837815132427)
          ·
            refine ⟨1414560410270756722698641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943040273513837815132427 1414560410270756722698641)
            ·
              refine ⟨1060920307703067542023981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414560410270756722698641 1060920307703067542023981)
              ·
                refine ⟨397845115388650328258993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1060920307703067542023981 397845115388650328258993)
                ·
                  refine ⟨298383836541487746194245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397845115388650328258993 298383836541487746194245)
                  ·
                    refine ⟨55946969351528952411421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298383836541487746194245 55946969351528952411421)
                    ·
                      rfl

theorem cell23_326869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_326869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326869 prefixEnd_326869 := by exact prefixLift 326869
  have htrace : WordTrace (prefixWord ++ tailWord_326869) baseStart_326869 baseEnd_326869 := by
    simpa [prefixWord, tailWord_326869, baseEnd_326869] using wordTrace_append hprefix tailTrace_326869
  have hstable : (prefixWord ++ tailWord_326869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326869).length < 2 ^ (prefixWord ++ tailWord_326869).sum := by decide
  have hdescent : baseEnd_326869 < baseStart_326869 := by decide
  rcases family_descends (prefixWord ++ tailWord_326869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326892 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_326892 : Nat := 118140960795 + 326892 * 2 ^ 59
def prefixEnd_326892 : Nat := 4983230072969 + 3 ^ 40 * 326892 * 2
def baseEnd_326892 : Nat := 167852718109640267246657

theorem tailTrace_326892 : CollatzResearch.WordTrace tailWord_326892 prefixEnd_326892 167852718109640267246657 := by
  unfold tailWord_326892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961365365866793776979465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7948487154489058369305953 5961365365866793776979465)
  ·
    refine ⟨4471024024400095332734599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5961365365866793776979465 4471024024400095332734599)
    ·
      refine ⟨6706536036600142999101899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4471024024400095332734599 6706536036600142999101899)
      ·
        refine ⟨10059804054900214498652849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6706536036600142999101899 10059804054900214498652849)
        ·
          refine ⟨7544853041175160873989637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10059804054900214498652849 7544853041175160873989637)
          ·
            refine ⟨1414659945220342663873057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7544853041175160873989637 1414659945220342663873057)
            ·
              refine ⟨1060994958915256997904793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1414659945220342663873057 1060994958915256997904793)
              ·
                refine ⟨795746219186442748428595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1060994958915256997904793 795746219186442748428595)
                ·
                  refine ⟨1193619328779664122642893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 795746219186442748428595 1193619328779664122642893)
                  ·
                    refine ⟨447607248292374045991085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1193619328779664122642893 447607248292374045991085)
                    ·
                      refine ⟨167852718109640267246657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 447607248292374045991085 167852718109640267246657)
                      ·
                        rfl

theorem cell23_326892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_326892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326892 prefixEnd_326892 := by exact prefixLift 326892
  have htrace : WordTrace (prefixWord ++ tailWord_326892) baseStart_326892 baseEnd_326892 := by
    simpa [prefixWord, tailWord_326892, baseEnd_326892] using wordTrace_append hprefix tailTrace_326892
  have hstable : (prefixWord ++ tailWord_326892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326892).length < 2 ^ (prefixWord ++ tailWord_326892).sum := by decide
  have hdescent : baseEnd_326892 < baseStart_326892 := by decide
  rcases family_descends (prefixWord ++ tailWord_326892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326893 : List Nat := [1, 5, 1, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_326893 : Nat := 118140960795 + 326893 * 2 ^ 59
def prefixEnd_326893 : Nat := 4983230072969 + 3 ^ 40 * 326893 * 2
def baseEnd_326893 : Nat := 167853231590294763334153

theorem tailTrace_326893 : CollatzResearch.WordTrace tailWord_326893 prefixEnd_326893 167853231590294763334153 := by
  unfold tailWord_326893
  simp only [CollatzResearch.WordTrace]
  refine ⟨11922767204729964724745333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7948511469819976483163555 11922767204729964724745333)
  ·
    refine ⟨1117759425443434192944875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11922767204729964724745333 1117759425443434192944875)
    ·
      refine ⟨1676639138165151289417313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1117759425443434192944875 1676639138165151289417313)
      ·
        refine ⟨1257479353623863467062985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1676639138165151289417313 1257479353623863467062985)
        ·
          refine ⟨943109515217897600297239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257479353623863467062985 943109515217897600297239)
          ·
            refine ⟨1414664272826846400445859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943109515217897600297239 1414664272826846400445859)
            ·
              refine ⟨2121996409240269600668789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414664272826846400445859 2121996409240269600668789)
              ·
                refine ⟨198937163366275275062699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2121996409240269600668789 198937163366275275062699)
                ·
                  refine ⟨298405745049412912594049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198937163366275275062699 298405745049412912594049)
                  ·
                    refine ⟨223804308787059684445537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 298405745049412912594049 223804308787059684445537)
                    ·
                      refine ⟨167853231590294763334153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223804308787059684445537 167853231590294763334153)
                      ·
                        rfl

theorem cell23_326893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_326893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326893 prefixEnd_326893 := by exact prefixLift 326893
  have htrace : WordTrace (prefixWord ++ tailWord_326893) baseStart_326893 baseEnd_326893 := by
    simpa [prefixWord, tailWord_326893, baseEnd_326893] using wordTrace_append hprefix tailTrace_326893
  have hstable : (prefixWord ++ tailWord_326893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326893).length < 2 ^ (prefixWord ++ tailWord_326893).sum := by decide
  have hdescent : baseEnd_326893 < baseStart_326893 := by decide
  rcases family_descends (prefixWord ++ tailWord_326893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326936 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 1, 3, 2]
def baseStart_326936 : Nat := 118140960795 + 326936 * 2 ^ 59
def prefixEnd_326936 : Nat := 4983230072969 + 3 ^ 40 * 326936 * 2
def baseEnd_326936 : Nat := 167875311258438095096455

theorem tailTrace_326936 : CollatzResearch.WordTrace tailWord_326936 prefixEnd_326936 167875311258438095096455 := by
  unfold tailWord_326936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962167771787091534280331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7949557029049455379040441 5962167771787091534280331)
  ·
    refine ⟨8943251657680637301420497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5962167771787091534280331 8943251657680637301420497)
    ·
      refine ⟨6707438743260477976065373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8943251657680637301420497 6707438743260477976065373)
      ·
        refine ⟨2515289528722679241024515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6707438743260477976065373 2515289528722679241024515)
        ·
          refine ⟨3772934293084018861536773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515289528722679241024515 3772934293084018861536773)
          ·
            refine ⟨707425179953253536538145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3772934293084018861536773 707425179953253536538145)
            ·
              refine ⟨530568884964940152403609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707425179953253536538145 530568884964940152403609)
              ·
                refine ⟨397926663723705114302707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 530568884964940152403609 397926663723705114302707)
                ·
                  refine ⟨596889995585557671454061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397926663723705114302707 596889995585557671454061)
                  ·
                    refine ⟨223833748344584126795273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596889995585557671454061 223833748344584126795273)
                    ·
                      refine ⟨167875311258438095096455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223833748344584126795273 167875311258438095096455)
                      ·
                        rfl

theorem cell23_326936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_326936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326936 prefixEnd_326936 := by exact prefixLift 326936
  have htrace : WordTrace (prefixWord ++ tailWord_326936) baseStart_326936 baseEnd_326936 := by
    simpa [prefixWord, tailWord_326936, baseEnd_326936] using wordTrace_append hprefix tailTrace_326936
  have hstable : (prefixWord ++ tailWord_326936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326936).length < 2 ^ (prefixWord ++ tailWord_326936).sum := by decide
  have hdescent : baseEnd_326936 < baseStart_326936 := by decide
  rcases family_descends (prefixWord ++ tailWord_326936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326952 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_326952 : Nat := 118140960795 + 326952 * 2 ^ 59
def prefixEnd_326952 : Nat := 4983230072969 + 3 ^ 40 * 326952 * 2
def baseEnd_326952 : Nat := 167883526948910032496381

theorem tailTrace_326952 : CollatzResearch.WordTrace tailWord_326952 prefixEnd_326952 167883526948910032496381 := by
  unfold tailWord_326952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962459555758108900571555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7949946074344145200762073 5962459555758108900571555)
  ·
    refine ⟨8943689333637163350857333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5962459555758108900571555 8943689333637163350857333)
    ·
      refine ⟨838470875028484064142875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8943689333637163350857333 838470875028484064142875)
      ·
        refine ⟨1257706312542726096214313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838470875028484064142875 1257706312542726096214313)
        ·
          refine ⟨943279734407044572160735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1257706312542726096214313 943279734407044572160735)
          ·
            refine ⟨1414919601610566858241103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943279734407044572160735 1414919601610566858241103)
            ·
              refine ⟨2122379402415850287361655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1414919601610566858241103 2122379402415850287361655)
              ·
                refine ⟨3183569103623775431042483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2122379402415850287361655 3183569103623775431042483)
                ·
                  refine ⟨4775353655435663146563725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183569103623775431042483 4775353655435663146563725)
                  ·
                    refine ⟨1790757620788373679961397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4775353655435663146563725 1790757620788373679961397)
                    ·
                      refine ⟨167883526948910032496381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1790757620788373679961397 167883526948910032496381)
                      ·
                        rfl

theorem cell23_326952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_326952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326952 prefixEnd_326952 := by exact prefixLift 326952
  have htrace : WordTrace (prefixWord ++ tailWord_326952) baseStart_326952 baseEnd_326952 := by
    simpa [prefixWord, tailWord_326952, baseEnd_326952] using wordTrace_append hprefix tailTrace_326952
  have hstable : (prefixWord ++ tailWord_326952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326952).length < 2 ^ (prefixWord ++ tailWord_326952).sum := by decide
  have hdescent : baseEnd_326952 < baseStart_326952 := by decide
  rcases family_descends (prefixWord ++ tailWord_326952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326972 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 7]
def baseStart_326972 : Nat := 118140960795 + 326972 * 2 ^ 59
def prefixEnd_326972 : Nat := 4983230072969 + 3 ^ 40 * 326972 * 2
def baseEnd_326972 : Nat := 18654866284666661582921

theorem tailTrace_326972 : CollatzResearch.WordTrace tailWord_326972 prefixEnd_326972 18654866284666661582921 := by
  unfold tailWord_326972
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962824285721880608435585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7950432380962507477914113 5962824285721880608435585)
  ·
    refine ⟨4472118214291410456326689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5962824285721880608435585 4472118214291410456326689)
    ·
      refine ⟨3354088660718557842245017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4472118214291410456326689 3354088660718557842245017)
      ·
        refine ⟨2515566495538918381683763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3354088660718557842245017 2515566495538918381683763)
        ·
          refine ⟨3773349743308377572525645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2515566495538918381683763 3773349743308377572525645)
          ·
            refine ⟨1415006153740641589697117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3773349743308377572525645 1415006153740641589697117)
            ·
              refine ⟨530627307652740596136419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1415006153740641589697117 530627307652740596136419)
              ·
                refine ⟨795940961479110894204629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530627307652740596136419 795940961479110894204629)
                ·
                  refine ⟨18654866284666661582921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 795940961479110894204629 18654866284666661582921)
                  ·
                    rfl

theorem cell23_326972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_326972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326972 prefixEnd_326972 := by exact prefixLift 326972
  have htrace : WordTrace (prefixWord ++ tailWord_326972) baseStart_326972 baseEnd_326972 := by
    simpa [prefixWord, tailWord_326972, baseEnd_326972] using wordTrace_append hprefix tailTrace_326972
  have hstable : (prefixWord ++ tailWord_326972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326972).length < 2 ^ (prefixWord ++ tailWord_326972).sum := by decide
  have hdescent : baseEnd_326972 < baseStart_326972 := by decide
  rcases family_descends (prefixWord ++ tailWord_326972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326983 : List Nat := [1, 1, 4, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_326983 : Nat := 118140960795 + 326983 * 2 ^ 59
def prefixEnd_326983 : Nat := 4983230072969 + 3 ^ 40 * 326983 * 2
def baseEnd_326983 : Nat := 167899444849199411208739

theorem tailTrace_326983 : CollatzResearch.WordTrace tailWord_326983 prefixEnd_326983 167899444849199411208739 := by
  unfold tailWord_326983
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926049774403910095521603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7950699849602606730347735 11926049774403910095521603)
  ·
    refine ⟨17889074661605865143282405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11926049774403910095521603 17889074661605865143282405)
    ·
      refine ⟨3354201499051099714365451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17889074661605865143282405 3354201499051099714365451)
      ·
        refine ⟨5031302248576649571548177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354201499051099714365451 5031302248576649571548177)
        ·
          refine ⟨3773476686432487178661133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5031302248576649571548177 3773476686432487178661133)
          ·
            refine ⟨1415053757412182691997925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3773476686432487178661133 1415053757412182691997925)
            ·
              refine ⟨265322579514784254749611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1415053757412182691997925 265322579514784254749611)
              ·
                refine ⟨397983869272176382124417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265322579514784254749611 397983869272176382124417)
                ·
                  refine ⟨298487901954132286593313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 397983869272176382124417 298487901954132286593313)
                  ·
                    refine ⟨223865926465599214944985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 298487901954132286593313 223865926465599214944985)
                    ·
                      refine ⟨167899444849199411208739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223865926465599214944985 167899444849199411208739)
                      ·
                        rfl

theorem cell23_326983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_326983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326983 prefixEnd_326983 := by exact prefixLift 326983
  have htrace : WordTrace (prefixWord ++ tailWord_326983) baseStart_326983 baseEnd_326983 := by
    simpa [prefixWord, tailWord_326983, baseEnd_326983] using wordTrace_append hprefix tailTrace_326983
  have hstable : (prefixWord ++ tailWord_326983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326983).length < 2 ^ (prefixWord ++ tailWord_326983).sum := by decide
  have hdescent : baseEnd_326983 < baseStart_326983 := by decide
  rcases family_descends (prefixWord ++ tailWord_326983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326985 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 3, 7]
def baseStart_326985 : Nat := 118140960795 + 326985 * 2 ^ 59
def prefixEnd_326985 : Nat := 4983230072969 + 3 ^ 40 * 326985 * 2
def baseEnd_326985 : Nat := 55966823936836134461243

theorem tailTrace_326985 : CollatzResearch.WordTrace tailWord_326985 prefixEnd_326985 55966823936836134461243 := by
  unfold tailWord_326985
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926122720396664437094409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7950748480264442958062939 11926122720396664437094409)
  ·
    refine ⟨8944592040297498327820807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11926122720396664437094409 8944592040297498327820807)
    ·
      refine ⟨13416888060446247491731211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8944592040297498327820807 13416888060446247491731211)
      ·
        refine ⟨20125332090669371237596817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13416888060446247491731211 20125332090669371237596817)
        ·
          refine ⟨15093999068002028428197613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20125332090669371237596817 15093999068002028428197613)
          ·
            refine ⟨5660249650500760660574105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15093999068002028428197613 5660249650500760660574105)
            ·
              refine ⟨4245187237875570495430579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5660249650500760660574105 4245187237875570495430579)
              ·
                refine ⟨6367780856813355743145869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4245187237875570495430579 6367780856813355743145869)
                ·
                  refine ⟨2387917821305008403679701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6367780856813355743145869 2387917821305008403679701)
                  ·
                    refine ⟨55966823936836134461243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2387917821305008403679701 55966823936836134461243)
                    ·
                      rfl

theorem cell23_326985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_326985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326985 prefixEnd_326985 := by exact prefixLift 326985
  have htrace : WordTrace (prefixWord ++ tailWord_326985) baseStart_326985 baseEnd_326985 := by
    simpa [prefixWord, tailWord_326985, baseEnd_326985] using wordTrace_append hprefix tailTrace_326985
  have hstable : (prefixWord ++ tailWord_326985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326985).length < 2 ^ (prefixWord ++ tailWord_326985).sum := by decide
  have hdescent : baseEnd_326985 < baseStart_326985 := by decide
  rcases family_descends (prefixWord ++ tailWord_326985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_326995 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7]
def baseStart_326995 : Nat := 118140960795 + 326995 * 2 ^ 59
def prefixEnd_326995 : Nat := 4983230072969 + 3 ^ 40 * 326995 * 2
def baseEnd_326995 : Nat := 167905606617053364258683

theorem tailTrace_326995 : CollatzResearch.WordTrace tailWord_326995 prefixEnd_326995 167905606617053364258683 := by
  unfold tailWord_326995
  simp only [CollatzResearch.WordTrace]
  refine ⟨11926487450360436144958439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7950991633573624096638959 11926487450360436144958439)
  ·
    refine ⟨17889731175540654217437659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11926487450360436144958439 17889731175540654217437659)
    ·
      refine ⟨26834596763310981326156489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17889731175540654217437659 26834596763310981326156489)
      ·
        refine ⟨20125947572483235994617367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26834596763310981326156489 20125947572483235994617367)
        ·
          refine ⟨30188921358724853991926051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20125947572483235994617367 30188921358724853991926051)
          ·
            refine ⟨45283382038087280987889077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30188921358724853991926051 45283382038087280987889077)
            ·
              refine ⟨4245317066070682592614601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45283382038087280987889077 4245317066070682592614601)
              ·
                refine ⟨3183987799553011944460951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4245317066070682592614601 3183987799553011944460951)
                ·
                  refine ⟨4775981699329517916691427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3183987799553011944460951 4775981699329517916691427)
                  ·
                    refine ⟨7163972548994276875037141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4775981699329517916691427 7163972548994276875037141)
                    ·
                      refine ⟨167905606617053364258683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7163972548994276875037141 167905606617053364258683)
                      ·
                        rfl

theorem cell23_326995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_326995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_326995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_326995 prefixEnd_326995 := by exact prefixLift 326995
  have htrace : WordTrace (prefixWord ++ tailWord_326995) baseStart_326995 baseEnd_326995 := by
    simpa [prefixWord, tailWord_326995, baseEnd_326995] using wordTrace_append hprefix tailTrace_326995
  have hstable : (prefixWord ++ tailWord_326995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_326995).length < 2 ^ (prefixWord ++ tailWord_326995).sum := by decide
  have hdescent : baseEnd_326995 < baseStart_326995 := by decide
  rcases family_descends (prefixWord ++ tailWord_326995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327002 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_327002 : Nat := 118140960795 + 327002 * 2 ^ 59
def prefixEnd_327002 : Nat := 4983230072969 + 3 ^ 40 * 327002 * 2
def baseEnd_327002 : Nat := 55969733660544945623717

theorem tailTrace_327002 : CollatzResearch.WordTrace tailWord_327002 prefixEnd_327002 55969733660544945623717 := by
  unfold tailWord_327002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981685690333769085115815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7951161840890050893642173 2981685690333769085115815)
  ·
    refine ⟨4472528535500653627673723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2981685690333769085115815 4472528535500653627673723)
    ·
      refine ⟨6708792803250980441510585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4472528535500653627673723 6708792803250980441510585)
      ·
        refine ⟨5031594602438235331132939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6708792803250980441510585 5031594602438235331132939)
        ·
          refine ⟨7547391903657352996699409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5031594602438235331132939 7547391903657352996699409)
          ·
            refine ⟨5660543927743014747524557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7547391903657352996699409 5660543927743014747524557)
            ·
              refine ⟨2122703972903630530321709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5660543927743014747524557 2122703972903630530321709)
              ·
                refine ⟨796013989838861448870641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2122703972903630530321709 796013989838861448870641)
                ·
                  refine ⟨597010492379146086652981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796013989838861448870641 597010492379146086652981)
                  ·
                    refine ⟨55969733660544945623717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 597010492379146086652981 55969733660544945623717)
                    ·
                      rfl

theorem cell23_327002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_327002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327002 prefixEnd_327002 := by exact prefixLift 327002
  have htrace : WordTrace (prefixWord ++ tailWord_327002) baseStart_327002 baseEnd_327002 := by
    simpa [prefixWord, tailWord_327002, baseEnd_327002] using wordTrace_append hprefix tailTrace_327002
  have hstable : (prefixWord ++ tailWord_327002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327002).length < 2 ^ (prefixWord ++ tailWord_327002).sum := by decide
  have hdescent : baseEnd_327002 < baseStart_327002 := by decide
  rcases family_descends (prefixWord ++ tailWord_327002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327012 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_327012 : Nat := 118140960795 + 327012 * 2 ^ 59
def prefixEnd_327012 : Nat := 4983230072969 + 3 ^ 40 * 327012 * 2
def baseEnd_327012 : Nat := 167914335788179797746105

theorem tailTrace_327012 : CollatzResearch.WordTrace tailWord_327012 prefixEnd_327012 167914335788179797746105 := by
  unfold tailWord_327012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5963553745649424024163645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7951404994199232032218193 5963553745649424024163645)
  ·
    refine ⟨2236332654618534009061367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5963553745649424024163645 2236332654618534009061367)
    ·
      refine ⟨3354498981927801013592051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2236332654618534009061367 3354498981927801013592051)
      ·
        refine ⟨5031748472891701520388077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3354498981927801013592051 5031748472891701520388077)
        ·
          refine ⟨1886905677334388070145529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5031748472891701520388077 1886905677334388070145529)
          ·
            refine ⟨1415179258000791052609147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1886905677334388070145529 1415179258000791052609147)
            ·
              refine ⟨2122768887001186578913721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415179258000791052609147 2122768887001186578913721)
              ·
                refine ⟨1592076665250889934185291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2122768887001186578913721 1592076665250889934185291)
                ·
                  refine ⟨2388114997876334901277937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592076665250889934185291 2388114997876334901277937)
                  ·
                    refine ⟨1791086248407251175958453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2388114997876334901277937 1791086248407251175958453)
                    ·
                      refine ⟨167914335788179797746105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1791086248407251175958453 167914335788179797746105)
                      ·
                        rfl

theorem cell23_327012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_327012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327012 prefixEnd_327012 := by exact prefixLift 327012
  have htrace : WordTrace (prefixWord ++ tailWord_327012) baseStart_327012 baseEnd_327012 := by
    simpa [prefixWord, tailWord_327012, baseEnd_327012] using wordTrace_append hprefix tailTrace_327012
  have hstable : (prefixWord ++ tailWord_327012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327012).length < 2 ^ (prefixWord ++ tailWord_327012).sum := by decide
  have hdescent : baseEnd_327012 < baseStart_327012 := by decide
  rcases family_descends (prefixWord ++ tailWord_327012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327032 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 9, 4]
def baseStart_327032 : Nat := 118140960795 + 327032 * 2 ^ 59
def prefixEnd_327032 : Nat := 4983230072969 + 3 ^ 40 * 327032 * 2
def baseEnd_327032 : Nat := 55974868467089906498671

theorem tailTrace_327032 : CollatzResearch.WordTrace tailWord_327032 prefixEnd_327032 55974868467089906498671 := by
  unfold tailWord_327032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5963918475613195732027675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7951891300817594309370233 5963918475613195732027675)
  ·
    refine ⟨8945877713419793598041513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5963918475613195732027675 8945877713419793598041513)
    ·
      refine ⟨6709408285064845198531135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8945877713419793598041513 6709408285064845198531135)
      ·
        refine ⟨10064112427597267797796703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6709408285064845198531135 10064112427597267797796703)
        ·
          refine ⟨15096168641395901696695055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10064112427597267797796703 15096168641395901696695055)
          ·
            refine ⟨22644252962093852545042583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15096168641395901696695055 22644252962093852545042583)
            ·
              refine ⟨33966379443140778817563875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22644252962093852545042583 33966379443140778817563875)
              ·
                refine ⟨50949569164711168226345813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33966379443140778817563875 50949569164711168226345813)
                ·
                  refine ⟨298532631824479501326245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50949569164711168226345813 298532631824479501326245)
                  ·
                    refine ⟨55974868467089906498671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298532631824479501326245 55974868467089906498671)
                    ·
                      rfl

theorem cell23_327032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_327032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327032 prefixEnd_327032 := by exact prefixLift 327032
  have htrace : WordTrace (prefixWord ++ tailWord_327032) baseStart_327032 baseEnd_327032 := by
    simpa [prefixWord, tailWord_327032, baseEnd_327032] using wordTrace_append hprefix tailTrace_327032
  have hstable : (prefixWord ++ tailWord_327032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327032).length < 2 ^ (prefixWord ++ tailWord_327032).sum := by decide
  have hdescent : baseEnd_327032 < baseStart_327032 := by decide
  rcases family_descends (prefixWord ++ tailWord_327032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327116 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 1, 5, 2]
def baseStart_327116 : Nat := 118140960795 + 327116 * 2 ^ 59
def prefixEnd_327116 : Nat := 4983230072969 + 3 ^ 40 * 327116 * 2
def baseEnd_327116 : Nat := 167967737776247390845627

theorem tailTrace_327116 : CollatzResearch.WordTrace tailWord_327116 prefixEnd_327116 167967737776247390845627 := by
  unfold tailWord_327116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5965450341461036905056601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7953933788614715873408801 5965450341461036905056601)
  ·
    refine ⟨4474087756095777678792451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5965450341461036905056601 4474087756095777678792451)
    ·
      refine ⟨6711131634143666518188677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4474087756095777678792451 6711131634143666518188677)
      ·
        refine ⟨1258337181401937472160377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6711131634143666518188677 1258337181401937472160377)
        ·
          refine ⟨943752886051453104120283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258337181401937472160377 943752886051453104120283)
          ·
            refine ⟨1415629329077179656180425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943752886051453104120283 1415629329077179656180425)
            ·
              refine ⟨1061721996807884742135319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1415629329077179656180425 1061721996807884742135319)
              ·
                refine ⟨1592582995211827113202979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061721996807884742135319 1592582995211827113202979)
                ·
                  refine ⟨2388874492817740669804469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1592582995211827113202979 2388874492817740669804469)
                  ·
                    refine ⟨223956983701663187794169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2388874492817740669804469 223956983701663187794169)
                    ·
                      refine ⟨167967737776247390845627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223956983701663187794169 167967737776247390845627)
                      ·
                        rfl

theorem cell23_327116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_327116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327116 prefixEnd_327116 := by exact prefixLift 327116
  have htrace : WordTrace (prefixWord ++ tailWord_327116) baseStart_327116 baseEnd_327116 := by
    simpa [prefixWord, tailWord_327116, baseEnd_327116] using wordTrace_append hprefix tailTrace_327116
  have hstable : (prefixWord ++ tailWord_327116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327116).length < 2 ^ (prefixWord ++ tailWord_327116).sum := by decide
  have hdescent : baseEnd_327116 < baseStart_327116 := by decide
  rcases family_descends (prefixWord ++ tailWord_327116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327133 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_327133 : Nat := 118140960795 + 327133 * 2 ^ 59
def prefixEnd_327133 : Nat := 4983230072969 + 3 ^ 40 * 327133 * 2
def baseEnd_327133 : Nat := 167976466947373824333049

theorem tailTrace_327133 : CollatzResearch.WordTrace tailWord_327133 prefixEnd_327133 167976466947373824333049 := by
  unfold tailWord_327133
  simp only [CollatzResearch.WordTrace]
  refine ⟨11931520723860485713482053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7954347149240323808988035 11931520723860485713482053)
  ·
    refine ⟨2237160135723841071277885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11931520723860485713482053 2237160135723841071277885)
    ·
      refine ⟨838935050896440401729207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2237160135723841071277885 838935050896440401729207)
      ·
        refine ⟨1258402576344660602593811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838935050896440401729207 1258402576344660602593811)
        ·
          refine ⟨1887603864516990903890717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1258402576344660602593811 1887603864516990903890717)
          ·
            refine ⟨707851449193871588959019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1887603864516990903890717 707851449193871588959019)
            ·
              refine ⟨1061777173790807383438529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707851449193871588959019 1061777173790807383438529)
              ·
                refine ⟨796332880343105537578897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1061777173790807383438529 796332880343105537578897)
                ·
                  refine ⟨597249660257329153184173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 796332880343105537578897 597249660257329153184173)
                  ·
                    refine ⟨223968622596498432444065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 597249660257329153184173 223968622596498432444065)
                    ·
                      refine ⟨167976466947373824333049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 223968622596498432444065 167976466947373824333049)
                      ·
                        rfl

theorem cell23_327133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_327133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327133 prefixEnd_327133 := by exact prefixLift 327133
  have htrace : WordTrace (prefixWord ++ tailWord_327133) baseStart_327133 baseEnd_327133 := by
    simpa [prefixWord, tailWord_327133, baseEnd_327133] using wordTrace_append hprefix tailTrace_327133
  have hstable : (prefixWord ++ tailWord_327133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327133).length < 2 ^ (prefixWord ++ tailWord_327133).sum := by decide
  have hdescent : baseEnd_327133 < baseStart_327133 := by decide
  rcases family_descends (prefixWord ++ tailWord_327133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327152 : List Nat := [2, 1, 1, 1, 3, 4, 1, 10]
def baseStart_327152 : Nat := 118140960795 + 327152 * 2 ^ 59
def prefixEnd_327152 : Nat := 4983230072969 + 3 ^ 40 * 327152 * 2
def baseEnd_327152 : Nat := 6221711965918861110943

theorem tailTrace_327152 : CollatzResearch.WordTrace tailWord_327152 prefixEnd_327152 6221711965918861110943 := by
  unfold tailWord_327152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966106855395825979211855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7954809140527767972282473 5966106855395825979211855)
  ·
    refine ⟨8949160283093738968817783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5966106855395825979211855 8949160283093738968817783)
    ·
      refine ⟨13423740424640608453226675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8949160283093738968817783 13423740424640608453226675)
      ·
        refine ⟨20135610636960912679840013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13423740424640608453226675 20135610636960912679840013)
        ·
          refine ⟨7550853988860342254940005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20135610636960912679840013 7550853988860342254940005)
          ·
            refine ⟨1415785122911314172801251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7550853988860342254940005 1415785122911314172801251)
            ·
              refine ⟨2123677684366971259201877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1415785122911314172801251 2123677684366971259201877)
              ·
                refine ⟨6221711965918861110943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2123677684366971259201877 6221711965918861110943)
                ·
                  rfl

theorem cell23_327152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 10].length) (baseStart_327152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327152 prefixEnd_327152 := by exact prefixLift 327152
  have htrace : WordTrace (prefixWord ++ tailWord_327152) baseStart_327152 baseEnd_327152 := by
    simpa [prefixWord, tailWord_327152, baseEnd_327152] using wordTrace_append hprefix tailTrace_327152
  have hstable : (prefixWord ++ tailWord_327152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327152).length < 2 ^ (prefixWord ++ tailWord_327152).sum := by decide
  have hdescent : baseEnd_327152 < baseStart_327152 := by decide
  rcases family_descends (prefixWord ++ tailWord_327152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327249 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_327249 : Nat := 118140960795 + 327249 * 2 ^ 59
def prefixEnd_327249 : Nat := 4983230072969 + 3 ^ 40 * 327249 * 2
def baseEnd_327249 : Nat := 168036030703295370482515

theorem tailTrace_327249 : CollatzResearch.WordTrace tailWord_327249 prefixEnd_327249 168036030703295370482515 := by
  unfold tailWord_327249
  simp only [CollatzResearch.WordTrace]
  refine ⟨11935751591440237524704801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7957167727626825016469867 11935751591440237524704801)
  ·
    refine ⟨8951813693580178143528601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11935751591440237524704801 8951813693580178143528601)
    ·
      refine ⟨6713860270185133607646451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8951813693580178143528601 6713860270185133607646451)
      ·
        refine ⟨10070790405277700411469677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6713860270185133607646451 10070790405277700411469677)
        ·
          refine ⟨3776546401979137654301129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10070790405277700411469677 3776546401979137654301129)
          ·
            refine ⟨2832409801484353240725847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3776546401979137654301129 2832409801484353240725847)
            ·
              refine ⟨4248614702226529861088771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832409801484353240725847 4248614702226529861088771)
              ·
                refine ⟨6372922053339794791633157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4248614702226529861088771 6372922053339794791633157)
                ·
                  refine ⟨1194922885001211523431217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6372922053339794791633157 1194922885001211523431217)
                  ·
                    refine ⟨896192163750908642573413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1194922885001211523431217 896192163750908642573413)
                    ·
                      refine ⟨168036030703295370482515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 896192163750908642573413 168036030703295370482515)
                      ·
                        rfl

theorem cell23_327249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_327249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327249 prefixEnd_327249 := by exact prefixLift 327249
  have htrace : WordTrace (prefixWord ++ tailWord_327249) baseStart_327249 baseEnd_327249 := by
    simpa [prefixWord, tailWord_327249, baseEnd_327249] using wordTrace_append hprefix tailTrace_327249
  have hstable : (prefixWord ++ tailWord_327249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327249).length < 2 ^ (prefixWord ++ tailWord_327249).sum := by decide
  have hdescent : baseEnd_327249 < baseStart_327249 := by decide
  rcases family_descends (prefixWord ++ tailWord_327249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327289 : List Nat := [1, 2, 1, 3, 3, 1, 1, 3, 1, 7]
def baseStart_327289 : Nat := 118140960795 + 327289 * 2 ^ 59
def prefixEnd_327289 : Nat := 4983230072969 + 3 ^ 40 * 327289 * 2
def baseEnd_327289 : Nat := 56018856643158404660777

theorem tailTrace_327289 : CollatzResearch.WordTrace tailWord_327289 prefixEnd_327289 56018856643158404660777 := by
  unfold tailWord_327289
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937210511295324356160921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7958140340863549570773947 11937210511295324356160921)
  ·
    refine ⟨8952907883471493267120691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11937210511295324356160921 8952907883471493267120691)
    ·
      refine ⟨13429361825207239900681037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8952907883471493267120691 13429361825207239900681037)
      ·
        refine ⟨5036010684452714962755389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13429361825207239900681037 5036010684452714962755389)
        ·
          refine ⟨1888504006669768111033271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5036010684452714962755389 1888504006669768111033271)
          ·
            refine ⟨2832756010004652166549907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1888504006669768111033271 2832756010004652166549907)
            ·
              refine ⟨4249134015006978249824861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2832756010004652166549907 4249134015006978249824861)
              ·
                refine ⟨1593425255627616843684323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4249134015006978249824861 1593425255627616843684323)
                ·
                  refine ⟨2390137883441425265526485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593425255627616843684323 2390137883441425265526485)
                  ·
                    refine ⟨56018856643158404660777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2390137883441425265526485 56018856643158404660777)
                    ·
                      rfl

theorem cell23_327289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_327289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327289 prefixEnd_327289 := by exact prefixLift 327289
  have htrace : WordTrace (prefixWord ++ tailWord_327289) baseStart_327289 baseEnd_327289 := by
    simpa [prefixWord, tailWord_327289, baseEnd_327289] using wordTrace_append hprefix tailTrace_327289
  have hstable : (prefixWord ++ tailWord_327289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327289).length < 2 ^ (prefixWord ++ tailWord_327289).sum := by decide
  have hdescent : baseEnd_327289 < baseStart_327289 := by decide
  rcases family_descends (prefixWord ++ tailWord_327289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327293 : List Nat := [1, 4, 1, 1, 4, 1, 3, 3, 5]
def baseStart_327293 : Nat := 118140960795 + 327293 * 2 ^ 59
def prefixEnd_327293 : Nat := 4983230072969 + 3 ^ 40 * 327293 * 2
def baseEnd_327293 : Nat := 18673180428010355370257

theorem tailTrace_327293 : CollatzResearch.WordTrace tailWord_327293 prefixEnd_327293 18673180428010355370257 := by
  unfold tailWord_327293
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937356403280833039306533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7958237602187222026204355 11937356403280833039306533)
  ·
    refine ⟨2238254325615156194869975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11937356403280833039306533 2238254325615156194869975)
    ·
      refine ⟨3357381488422734292304963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238254325615156194869975 3357381488422734292304963)
      ·
        refine ⟨5036072232634101438457445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357381488422734292304963 5036072232634101438457445)
        ·
          refine ⟨944263543618894019710771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5036072232634101438457445 944263543618894019710771)
          ·
            refine ⟨1416395315428341029566157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944263543618894019710771 1416395315428341029566157)
            ·
              refine ⟨531148243285627886087309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1416395315428341029566157 531148243285627886087309)
              ·
                refine ⟨199180591232110457282741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531148243285627886087309 199180591232110457282741)
                ·
                  refine ⟨18673180428010355370257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199180591232110457282741 18673180428010355370257)
                  ·
                    rfl

theorem cell23_327293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_327293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327293 prefixEnd_327293 := by exact prefixLift 327293
  have htrace : WordTrace (prefixWord ++ tailWord_327293) baseStart_327293 baseEnd_327293 := by
    simpa [prefixWord, tailWord_327293, baseEnd_327293] using wordTrace_append hprefix tailTrace_327293
  have hstable : (prefixWord ++ tailWord_327293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327293).length < 2 ^ (prefixWord ++ tailWord_327293).sum := by decide
  have hdescent : baseEnd_327293 < baseStart_327293 := by decide
  rcases family_descends (prefixWord ++ tailWord_327293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327299 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5]
def baseStart_327299 : Nat := 118140960795 + 327299 * 2 ^ 59
def prefixEnd_327299 : Nat := 4983230072969 + 3 ^ 40 * 327299 * 2
def baseEnd_327299 : Nat := 168061704736020174857285

theorem tailTrace_327299 : CollatzResearch.WordTrace tailWord_327299 prefixEnd_327299 168061704736020174857285 := by
  unfold tailWord_327299
  simp only [CollatzResearch.WordTrace]
  refine ⟨11937575241259096064024951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7958383494172730709349967 11937575241259096064024951)
  ·
    refine ⟨17906362861888644096037427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11937575241259096064024951 17906362861888644096037427)
    ·
      refine ⟨26859544292832966144056141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17906362861888644096037427 26859544292832966144056141)
      ·
        refine ⟨10072329109812362304021053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26859544292832966144056141 10072329109812362304021053)
        ·
          refine ⟨3777123416179635864007895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10072329109812362304021053 3777123416179635864007895)
          ·
            refine ⟨5665685124269453796011843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3777123416179635864007895 5665685124269453796011843)
            ·
              refine ⟨8498527686404180694017765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5665685124269453796011843 8498527686404180694017765)
              ·
                refine ⟨1593473941200783880128331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8498527686404180694017765 1593473941200783880128331)
                ·
                  refine ⟨2390210911801175820192497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593473941200783880128331 2390210911801175820192497)
                  ·
                    refine ⟨1792658183850881865144373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2390210911801175820192497 1792658183850881865144373)
                    ·
                      refine ⟨168061704736020174857285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1792658183850881865144373 168061704736020174857285)
                      ·
                        rfl

theorem cell23_327299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_327299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327299 prefixEnd_327299 := by exact prefixLift 327299
  have htrace : WordTrace (prefixWord ++ tailWord_327299) baseStart_327299 baseEnd_327299 := by
    simpa [prefixWord, tailWord_327299, baseEnd_327299] using wordTrace_append hprefix tailTrace_327299
  have hstable : (prefixWord ++ tailWord_327299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327299).length < 2 ^ (prefixWord ++ tailWord_327299).sum := by decide
  have hdescent : baseEnd_327299 < baseStart_327299 := by decide
  rcases family_descends (prefixWord ++ tailWord_327299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327306 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_327306 : Nat := 118140960795 + 327306 * 2 ^ 59
def prefixEnd_327306 : Nat := 4983230072969 + 3 ^ 40 * 327306 * 2
def baseEnd_327306 : Nat := 56021766366867215823251

theorem tailTrace_327306 : CollatzResearch.WordTrace tailWord_327306 prefixEnd_327306 56021766366867215823251 := by
  unfold tailWord_327306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984457638058434064882443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7958553701489157506353181 2984457638058434064882443)
  ·
    refine ⟨4476686457087651097323665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2984457638058434064882443 4476686457087651097323665)
    ·
      refine ⟨3357514842815738322992749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4476686457087651097323665 3357514842815738322992749)
      ·
        refine ⟨1259068066055901871122281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3357514842815738322992749 1259068066055901871122281)
        ·
          refine ⟨944301049541926403341711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259068066055901871122281 944301049541926403341711)
          ·
            refine ⟨1416451574312889605012567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944301049541926403341711 1416451574312889605012567)
            ·
              refine ⟨2124677361469334407518851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1416451574312889605012567 2124677361469334407518851)
              ·
                refine ⟨3187016042204001611278277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2124677361469334407518851 3187016042204001611278277)
                ·
                  refine ⟨597565507913250302114677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3187016042204001611278277 597565507913250302114677)
                  ·
                    refine ⟨56021766366867215823251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 597565507913250302114677 56021766366867215823251)
                    ·
                      rfl

theorem cell23_327306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_327306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327306 prefixEnd_327306 := by exact prefixLift 327306
  have htrace : WordTrace (prefixWord ++ tailWord_327306) baseStart_327306 baseEnd_327306 := by
    simpa [prefixWord, tailWord_327306, baseEnd_327306] using wordTrace_append hprefix tailTrace_327306
  have hstable : (prefixWord ++ tailWord_327306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327306).length < 2 ^ (prefixWord ++ tailWord_327306).sum := by decide
  have hdescent : baseEnd_327306 < baseStart_327306 := by decide
  rcases family_descends (prefixWord ++ tailWord_327306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327310 : List Nat := [4, 1, 1, 3, 1, 3, 3, 2, 5]
def baseStart_327310 : Nat := 118140960795 + 327310 * 2 ^ 59
def prefixEnd_327310 : Nat := 4983230072969 + 3 ^ 40 * 327310 * 2
def baseEnd_327310 : Nat := 18674150335913292424415

theorem tailTrace_327310 : CollatzResearch.WordTrace tailWord_327310 prefixEnd_327310 18674150335913292424415 := by
  unfold tailWord_327310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492247055527405617834423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7958650962812829961783589 1492247055527405617834423)
  ·
    refine ⟨2238370583291108426751635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1492247055527405617834423 2238370583291108426751635)
    ·
      refine ⟨3357555874936662640127453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238370583291108426751635 3357555874936662640127453)
      ·
        refine ⟨1259083453101248490047795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3357555874936662640127453 1259083453101248490047795)
        ·
          refine ⟨1888625179651872735071693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259083453101248490047795 1888625179651872735071693)
          ·
            refine ⟨708234442369452275651885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1888625179651872735071693 708234442369452275651885)
            ·
              refine ⟨265587915888544603369457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708234442369452275651885 265587915888544603369457)
              ·
                refine ⟨199190936916408452527093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265587915888544603369457 199190936916408452527093)
                ·
                  refine ⟨18674150335913292424415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199190936916408452527093 18674150335913292424415)
                  ·
                    rfl

theorem cell23_327310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_327310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327310 prefixEnd_327310 := by exact prefixLift 327310
  have htrace : WordTrace (prefixWord ++ tailWord_327310) baseStart_327310 baseEnd_327310 := by
    simpa [prefixWord, tailWord_327310, baseEnd_327310] using wordTrace_append hprefix tailTrace_327310
  have hstable : (prefixWord ++ tailWord_327310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327310).length < 2 ^ (prefixWord ++ tailWord_327310).sum := by decide
  have hdescent : baseEnd_327310 < baseStart_327310 := by decide
  rcases family_descends (prefixWord ++ tailWord_327310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327346 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_327346 : Nat := 118140960795 + 327346 * 2 ^ 59
def prefixEnd_327346 : Nat := 4983230072969 + 3 ^ 40 * 327346 * 2
def baseEnd_327346 : Nat := 168085838326781490969569

theorem tailTrace_327346 : CollatzResearch.WordTrace tailWord_327346 prefixEnd_327346 168085838326781490969569 := by
  unfold tailWord_327346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2984822368022205772746473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7959526314725882060657261 2984822368022205772746473)
  ·
    refine ⟨2238616776016654329559855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2984822368022205772746473 2238616776016654329559855)
    ·
      refine ⟨3357925164024981494339783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238616776016654329559855 3357925164024981494339783)
      ·
        refine ⟨5036887746037472241509675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3357925164024981494339783 5036887746037472241509675)
        ·
          refine ⟨7555331619056208362264513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5036887746037472241509675 7555331619056208362264513)
          ·
            refine ⟨5666498714292156271698385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7555331619056208362264513 5666498714292156271698385)
            ·
              refine ⟨4249874035719117203773789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5666498714292156271698385 4249874035719117203773789)
              ·
                refine ⟨1593702763394668951415171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4249874035719117203773789 1593702763394668951415171)
                ·
                  refine ⟨2390554145092003427122757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1593702763394668951415171 2390554145092003427122757)
                  ·
                    refine ⟨448228902204750642585517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2390554145092003427122757 448228902204750642585517)
                    ·
                      refine ⟨168085838326781490969569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 448228902204750642585517 168085838326781490969569)
                      ·
                        rfl

theorem cell23_327346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_327346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327346 prefixEnd_327346 := by exact prefixLift 327346
  have htrace : WordTrace (prefixWord ++ tailWord_327346) baseStart_327346 baseEnd_327346 := by
    simpa [prefixWord, tailWord_327346, baseEnd_327346] using wordTrace_append hprefix tailTrace_327346
  have hstable : (prefixWord ++ tailWord_327346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327346).length < 2 ^ (prefixWord ++ tailWord_327346).sum := by decide
  have hdescent : baseEnd_327346 < baseStart_327346 := by decide
  rcases family_descends (prefixWord ++ tailWord_327346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327396 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_327396 : Nat := 118140960795 + 327396 * 2 ^ 59
def prefixEnd_327396 : Nat := 4983230072969 + 3 ^ 40 * 327396 * 2
def baseEnd_327396 : Nat := 56037170786502098448113

theorem tailTrace_327396 : CollatzResearch.WordTrace tailWord_327396 prefixEnd_327396 56037170786502098448113 := by
  unfold tailWord_327396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970556560953840815153021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7960742081271787753537361 5970556560953840815153021)
  ·
    refine ⟨2238958710357690305682383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5970556560953840815153021 2238958710357690305682383)
    ·
      refine ⟨3358438065536535458523575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2238958710357690305682383 3358438065536535458523575)
      ·
        refine ⟨5037657098304803187785363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3358438065536535458523575 5037657098304803187785363)
        ·
          refine ⟨7556485647457204781678045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5037657098304803187785363 7556485647457204781678045)
          ·
            refine ⟨2833682117796451793129267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7556485647457204781678045 2833682117796451793129267)
            ·
              refine ⟨4250523176694677689693901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2833682117796451793129267 4250523176694677689693901)
              ·
                refine ⟨1593946191260504133635213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4250523176694677689693901 1593946191260504133635213)
                ·
                  refine ⟨597729821722689050113205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1593946191260504133635213 597729821722689050113205)
                  ·
                    refine ⟨56037170786502098448113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 597729821722689050113205 56037170786502098448113)
                    ·
                      rfl

theorem cell23_327396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_327396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327396 prefixEnd_327396 := by exact prefixLift 327396
  have htrace : WordTrace (prefixWord ++ tailWord_327396) baseStart_327396 baseEnd_327396 := by
    simpa [prefixWord, tailWord_327396, baseEnd_327396] using wordTrace_append hprefix tailTrace_327396
  have hstable : (prefixWord ++ tailWord_327396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327396).length < 2 ^ (prefixWord ++ tailWord_327396).sum := by decide
  have hdescent : baseEnd_327396 < baseStart_327396 := by decide
  rcases family_descends (prefixWord ++ tailWord_327396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327416 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_327416 : Nat := 118140960795 + 327416 * 2 ^ 59
def prefixEnd_327416 : Nat := 4983230072969 + 3 ^ 40 * 327416 * 2
def baseEnd_327416 : Nat := 168121781972596217094247

theorem tailTrace_327416 : CollatzResearch.WordTrace tailWord_327416 prefixEnd_327416 168121781972596217094247 := by
  unfold tailWord_327416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5970921290917612523017051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7961228387890150030689401 5970921290917612523017051)
  ·
    refine ⟨8956381936376418784525577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5970921290917612523017051 8956381936376418784525577)
    ·
      refine ⟨6717286452282314088394183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8956381936376418784525577 6717286452282314088394183)
      ·
        refine ⟨10075929678423471132591275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6717286452282314088394183 10075929678423471132591275)
        ·
          refine ⟨15113894517635206698886913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10075929678423471132591275 15113894517635206698886913)
          ·
            refine ⟨11335420888226405024165185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15113894517635206698886913 11335420888226405024165185)
            ·
              refine ⟨8501565666169803768123889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11335420888226405024165185 8501565666169803768123889)
              ·
                refine ⟨6376174249627352826092917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8501565666169803768123889 6376174249627352826092917)
                ·
                  refine ⟨597766335902564327446211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6376174249627352826092917 597766335902564327446211)
                  ·
                    refine ⟨896649503853846491169317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 597766335902564327446211 896649503853846491169317)
                    ·
                      refine ⟨168121781972596217094247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 896649503853846491169317 168121781972596217094247)
                      ·
                        rfl

theorem cell23_327416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_327416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327416 prefixEnd_327416 := by exact prefixLift 327416
  have htrace : WordTrace (prefixWord ++ tailWord_327416) baseStart_327416 baseEnd_327416 := by
    simpa [prefixWord, tailWord_327416, baseEnd_327416] using wordTrace_append hprefix tailTrace_327416
  have hstable : (prefixWord ++ tailWord_327416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327416).length < 2 ^ (prefixWord ++ tailWord_327416).sum := by decide
  have hdescent : baseEnd_327416 < baseStart_327416 := by decide
  rcases family_descends (prefixWord ++ tailWord_327416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327436 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_327436 : Nat := 118140960795 + 327436 * 2 ^ 59
def prefixEnd_327436 : Nat := 4983230072969 + 3 ^ 40 * 327436 * 2
def baseEnd_327436 : Nat := 168132051585686138844155

theorem tailTrace_327436 : CollatzResearch.WordTrace tailWord_327436 prefixEnd_327436 168132051585686138844155 := by
  unfold tailWord_327436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971286020881384230881081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7961714694508512307841441 5971286020881384230881081)
  ·
    refine ⟨4478464515661038173160811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5971286020881384230881081 4478464515661038173160811)
    ·
      refine ⟨6717696773491557259741217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4478464515661038173160811 6717696773491557259741217)
      ·
        refine ⟨5038272580118667944805913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6717696773491557259741217 5038272580118667944805913)
        ·
          refine ⟨3778704435089000958604435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5038272580118667944805913 3778704435089000958604435)
          ·
            refine ⟨5668056652633501437906653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3778704435089000958604435 5668056652633501437906653)
            ·
              refine ⟨2125521244737563039214995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5668056652633501437906653 2125521244737563039214995)
              ·
                refine ⟨3188281867106344558822493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2125521244737563039214995 3188281867106344558822493)
                ·
                  refine ⟨1195605700164879209558435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3188281867106344558822493 1195605700164879209558435)
                  ·
                    refine ⟨1793408550247318814337653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1195605700164879209558435 1793408550247318814337653)
                    ·
                      refine ⟨168132051585686138844155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1793408550247318814337653 168132051585686138844155)
                      ·
                        rfl

theorem cell23_327436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_327436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327436 prefixEnd_327436 := by exact prefixLift 327436
  have htrace : WordTrace (prefixWord ++ tailWord_327436) baseStart_327436 baseEnd_327436 := by
    simpa [prefixWord, tailWord_327436, baseEnd_327436] using wordTrace_append hprefix tailTrace_327436
  have hstable : (prefixWord ++ tailWord_327436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327436).length < 2 ^ (prefixWord ++ tailWord_327436).sum := by decide
  have hdescent : baseEnd_327436 < baseStart_327436 := by decide
  rcases family_descends (prefixWord ++ tailWord_327436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327450 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_327450 : Nat := 118140960795 + 327450 * 2 ^ 59
def prefixEnd_327450 : Nat := 4983230072969 + 3 ^ 40 * 327450 * 2
def baseEnd_327450 : Nat := 168139240314849084069091

theorem tailTrace_327450 : CollatzResearch.WordTrace tailWord_327450 prefixEnd_327450 168139240314849084069091 := by
  unfold tailWord_327450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985770665928012213192951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7962055109141365901847869 2985770665928012213192951)
  ·
    refine ⟨4478655998892018319789427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2985770665928012213192951 4478655998892018319789427)
    ·
      refine ⟨6717983998338027479684141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4478655998892018319789427 6717983998338027479684141)
      ·
        refine ⟨2519243999376760304881553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6717983998338027479684141 2519243999376760304881553)
        ·
          refine ⟨1889432999532570228661165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2519243999376760304881553 1889432999532570228661165)
          ·
            refine ⟨708537374824713835747937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1889432999532570228661165 708537374824713835747937)
            ·
              refine ⟨531403031118535376810953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708537374824713835747937 531403031118535376810953)
              ·
                refine ⟨398552273338901532608215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531403031118535376810953 398552273338901532608215)
                ·
                  refine ⟨597828410008352298912323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398552273338901532608215 597828410008352298912323)
                  ·
                    refine ⟨896742615012528448368485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 597828410008352298912323 896742615012528448368485)
                    ·
                      refine ⟨168139240314849084069091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 896742615012528448368485 168139240314849084069091)
                      ·
                        rfl

theorem cell23_327450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_327450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327450 prefixEnd_327450 := by exact prefixLift 327450
  have htrace : WordTrace (prefixWord ++ tailWord_327450) baseStart_327450 baseEnd_327450 := by
    simpa [prefixWord, tailWord_327450, baseEnd_327450] using wordTrace_append hprefix tailTrace_327450
  have hstable : (prefixWord ++ tailWord_327450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327450).length < 2 ^ (prefixWord ++ tailWord_327450).sum := by decide
  have hdescent : baseEnd_327450 < baseStart_327450 := by decide
  rcases family_descends (prefixWord ++ tailWord_327450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327456 : List Nat := [2, 1, 1, 5, 1, 1, 3, 9]
def baseStart_327456 : Nat := 118140960795 + 327456 * 2 ^ 59
def prefixEnd_327456 : Nat := 4983230072969 + 3 ^ 40 * 327456 * 2
def baseEnd_327456 : Nat := 6227493377732446688669

theorem tailTrace_327456 : CollatzResearch.WordTrace tailWord_327456 prefixEnd_327456 6227493377732446688669 := by
  unfold tailWord_327456
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971650750845155938745111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7962201001126874584993481 5971650750845155938745111)
  ·
    refine ⟨8957476126267733908117667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5971650750845155938745111 8957476126267733908117667)
    ·
      refine ⟨13436214189401600862176501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8957476126267733908117667 13436214189401600862176501)
      ·
        refine ⟨1259645080256400080829047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13436214189401600862176501 1259645080256400080829047)
        ·
          refine ⟨1889467620384600121243571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259645080256400080829047 1889467620384600121243571)
          ·
            refine ⟨2834201430576900181865357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889467620384600121243571 2834201430576900181865357)
            ·
              refine ⟨1062825536466337568199509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2834201430576900181865357 1062825536466337568199509)
              ·
                refine ⟨6227493377732446688669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1062825536466337568199509 6227493377732446688669)
                ·
                  rfl

theorem cell23_327456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 9].length) (baseStart_327456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327456 prefixEnd_327456 := by exact prefixLift 327456
  have htrace : WordTrace (prefixWord ++ tailWord_327456) baseStart_327456 baseEnd_327456 := by
    simpa [prefixWord, tailWord_327456, baseEnd_327456] using wordTrace_append hprefix tailTrace_327456
  have hstable : (prefixWord ++ tailWord_327456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327456).length < 2 ^ (prefixWord ++ tailWord_327456).sum := by decide
  have hdescent : baseEnd_327456 < baseStart_327456 := by decide
  rcases family_descends (prefixWord ++ tailWord_327456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327494 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_327494 : Nat := 118140960795 + 327494 * 2 ^ 59
def prefixEnd_327494 : Nat := 4983230072969 + 3 ^ 40 * 327494 * 2
def baseEnd_327494 : Nat := 56053944487882303972963

theorem tailTrace_327494 : CollatzResearch.WordTrace tailWord_327494 prefixEnd_327494 56053944487882303972963 := by
  unfold tailWord_327494
  simp only [CollatzResearch.WordTrace]
  refine ⟨373271483611020136480423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7963124983701762911582357 373271483611020136480423)
  ·
    refine ⟨559907225416530204720635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 373271483611020136480423 559907225416530204720635)
    ·
      refine ⟨839860838124795307080953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559907225416530204720635 839860838124795307080953)
      ·
        refine ⟨629895628593596480310715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839860838124795307080953 629895628593596480310715)
        ·
          refine ⟨944843442890394720466073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629895628593596480310715 944843442890394720466073)
          ·
            refine ⟨708632582167796040349555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 944843442890394720466073 708632582167796040349555)
            ·
              refine ⟨1062948873251694060524333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708632582167796040349555 1062948873251694060524333)
              ·
                refine ⟨398605827469385272696625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1062948873251694060524333 398605827469385272696625)
                ·
                  refine ⟨298954370602038954522469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398605827469385272696625 298954370602038954522469)
                  ·
                    refine ⟨56053944487882303972963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298954370602038954522469 56053944487882303972963)
                    ·
                      rfl

theorem cell23_327494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_327494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327494 prefixEnd_327494 := by exact prefixLift 327494
  have htrace : WordTrace (prefixWord ++ tailWord_327494) baseStart_327494 baseEnd_327494 := by
    simpa [prefixWord, tailWord_327494, baseEnd_327494] using wordTrace_append hprefix tailTrace_327494
  have hstable : (prefixWord ++ tailWord_327494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327494).length < 2 ^ (prefixWord ++ tailWord_327494).sum := by decide
  have hdescent : baseEnd_327494 < baseStart_327494 := by decide
  rcases family_descends (prefixWord ++ tailWord_327494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327534 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_327534 : Nat := 118140960795 + 327534 * 2 ^ 59
def prefixEnd_327534 : Nat := 4983230072969 + 3 ^ 40 * 327534 * 2
def baseEnd_327534 : Nat := 168182372689826755418705

theorem tailTrace_327534 : CollatzResearch.WordTrace tailWord_327534 prefixEnd_327534 168182372689826755418705 := by
  unfold tailWord_327534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493268299425966399853707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7964097596938487465886437 1493268299425966399853707)
  ·
    refine ⟨2239902449138949599780561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1493268299425966399853707 2239902449138949599780561)
    ·
      refine ⟨1679926836854212199835421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2239902449138949599780561 1679926836854212199835421)
      ·
        refine ⟨629972563820329574938283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1679926836854212199835421 629972563820329574938283)
        ·
          refine ⟨944958845730494362407425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629972563820329574938283 944958845730494362407425)
          ·
            refine ⟨708719134297870771805569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 944958845730494362407425 708719134297870771805569)
            ·
              refine ⟨531539350723403078854177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708719134297870771805569 531539350723403078854177)
              ·
                refine ⟨398654513042552309140633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531539350723403078854177 398654513042552309140633)
                ·
                  refine ⟨298990884781914231855475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398654513042552309140633 298990884781914231855475)
                  ·
                    refine ⟨448486327172871347783213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 298990884781914231855475 448486327172871347783213)
                    ·
                      refine ⟨168182372689826755418705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 448486327172871347783213 168182372689826755418705)
                      ·
                        rfl

theorem cell23_327534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_327534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327534 prefixEnd_327534 := by exact prefixLift 327534
  have htrace : WordTrace (prefixWord ++ tailWord_327534) baseStart_327534 baseEnd_327534 := by
    simpa [prefixWord, tailWord_327534, baseEnd_327534] using wordTrace_append hprefix tailTrace_327534
  have hstable : (prefixWord ++ tailWord_327534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327534).length < 2 ^ (prefixWord ++ tailWord_327534).sum := by decide
  have hdescent : baseEnd_327534 < baseStart_327534 := by decide
  rcases family_descends (prefixWord ++ tailWord_327534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327536 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_327536 : Nat := 118140960795 + 327536 * 2 ^ 59
def prefixEnd_327536 : Nat := 4983230072969 + 3 ^ 40 * 327536 * 2
def baseEnd_327536 : Nat := 168183399651135747593695

theorem tailTrace_327536 : CollatzResearch.WordTrace tailWord_327536 prefixEnd_327536 168183399651135747593695 := by
  unfold tailWord_327536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973109670700242770201231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7964146227600323693601641 5973109670700242770201231)
  ·
    refine ⟨8959664506050364155301847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5973109670700242770201231 8959664506050364155301847)
    ·
      refine ⟨13439496759075546232952771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8959664506050364155301847 13439496759075546232952771)
      ·
        refine ⟨20159245138613319349429157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13439496759075546232952771 20159245138613319349429157)
        ·
          refine ⟨3779858463489997378017967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20159245138613319349429157 3779858463489997378017967)
          ·
            refine ⟨5669787695234996067026951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3779858463489997378017967 5669787695234996067026951)
            ·
              refine ⟨8504681542852494100540427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5669787695234996067026951 8504681542852494100540427)
              ·
                refine ⟨12757022314278741150810641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8504681542852494100540427 12757022314278741150810641)
                ·
                  refine ⟨9567766735709055863107981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12757022314278741150810641 9567766735709055863107981)
                  ·
                    refine ⟨3587912525890895948665493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9567766735709055863107981 3587912525890895948665493)
                    ·
                      refine ⟨168183399651135747593695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3587912525890895948665493 168183399651135747593695)
                      ·
                        rfl

theorem cell23_327536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_327536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327536 prefixEnd_327536 := by exact prefixLift 327536
  have htrace : WordTrace (prefixWord ++ tailWord_327536) baseStart_327536 baseEnd_327536 := by
    simpa [prefixWord, tailWord_327536, baseEnd_327536] using wordTrace_append hprefix tailTrace_327536
  have hstable : (prefixWord ++ tailWord_327536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327536).length < 2 ^ (prefixWord ++ tailWord_327536).sum := by decide
  have hdescent : baseEnd_327536 < baseStart_327536 := by decide
  rcases family_descends (prefixWord ++ tailWord_327536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327550 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_327550 : Nat := 118140960795 + 327550 * 2 ^ 59
def prefixEnd_327550 : Nat := 4983230072969 + 3 ^ 40 * 327550 * 2
def baseEnd_327550 : Nat := 56063529460099564272877

theorem tailTrace_327550 : CollatzResearch.WordTrace tailWord_327550 prefixEnd_327550 56063529460099564272877 := by
  unfold tailWord_327550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493341245418720741426513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7964486642233177287608069 1493341245418720741426513)
  ·
    refine ⟨1120005934064040556069885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1493341245418720741426513 1120005934064040556069885)
    ·
      refine ⟨420002225274015208526207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1120005934064040556069885 420002225274015208526207)
      ·
        refine ⟨630003337911022812789311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420002225274015208526207 630003337911022812789311)
        ·
          refine ⟨945005006866534219183967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630003337911022812789311 945005006866534219183967)
          ·
            refine ⟨1417507510299801328775951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945005006866534219183967 1417507510299801328775951)
            ·
              refine ⟨2126261265449701993163927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1417507510299801328775951 2126261265449701993163927)
              ·
                refine ⟨3189391898174552989745891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2126261265449701993163927 3189391898174552989745891)
                ·
                  refine ⟨4784087847261829484618837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189391898174552989745891 4784087847261829484618837)
                  ·
                    refine ⟨56063529460099564272877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4784087847261829484618837 56063529460099564272877)
                    ·
                      rfl

theorem cell23_327550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_327550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327550 prefixEnd_327550 := by exact prefixLift 327550
  have htrace : WordTrace (prefixWord ++ tailWord_327550) baseStart_327550 baseEnd_327550 := by
    simpa [prefixWord, tailWord_327550, baseEnd_327550] using wordTrace_append hprefix tailTrace_327550
  have hstable : (prefixWord ++ tailWord_327550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327550).length < 2 ^ (prefixWord ++ tailWord_327550).sum := by decide
  have hdescent : baseEnd_327550 < baseStart_327550 := by decide
  rcases family_descends (prefixWord ++ tailWord_327550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327557 : List Nat := [1, 3, 1, 1, 3, 2, 1, 5, 2, 2, 2]
def baseStart_327557 : Nat := 118140960795 + 327557 * 2 ^ 59
def prefixEnd_327557 : Nat := 4983230072969 + 3 ^ 40 * 327557 * 2
def baseEnd_327557 : Nat := 168194182744880165431099

theorem tailTrace_327557 : CollatzResearch.WordTrace tailWord_327557 prefixEnd_327557 168194182744880165431099 := by
  unfold tailWord_327557
  simp only [CollatzResearch.WordTrace]
  refine ⟨11946985274324406126916925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7964656849549604084611283 11946985274324406126916925)
  ·
    refine ⟨4480119477871652297593847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11946985274324406126916925 4480119477871652297593847)
    ·
      refine ⟨6720179216807478446390771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4480119477871652297593847 6720179216807478446390771)
      ·
        refine ⟨10080268825211217669586157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6720179216807478446390771 10080268825211217669586157)
        ·
          refine ⟨3780100809454206626094809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10080268825211217669586157 3780100809454206626094809)
          ·
            refine ⟨2835075607090654969571107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3780100809454206626094809 2835075607090654969571107)
            ·
              refine ⟨4252613410635982454356661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835075607090654969571107 4252613410635982454356661)
              ·
                refine ⟨398682507247123355095937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4252613410635982454356661 398682507247123355095937)
                ·
                  refine ⟨299011880435342516321953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398682507247123355095937 299011880435342516321953)
                  ·
                    refine ⟨224258910326506887241465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299011880435342516321953 224258910326506887241465)
                    ·
                      refine ⟨168194182744880165431099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 224258910326506887241465 168194182744880165431099)
                      ·
                        rfl

theorem cell23_327557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_327557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327557 prefixEnd_327557 := by exact prefixLift 327557
  have htrace : WordTrace (prefixWord ++ tailWord_327557) baseStart_327557 baseEnd_327557 := by
    simpa [prefixWord, tailWord_327557, baseEnd_327557] using wordTrace_append hprefix tailTrace_327557
  have hstable : (prefixWord ++ tailWord_327557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327557).length < 2 ^ (prefixWord ++ tailWord_327557).sum := by decide
  have hdescent : baseEnd_327557 < baseStart_327557 := by decide
  rcases family_descends (prefixWord ++ tailWord_327557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327573 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_327573 : Nat := 118140960795 + 327573 * 2 ^ 59
def prefixEnd_327573 : Nat := 4983230072969 + 3 ^ 40 * 327573 * 2
def baseEnd_327573 : Nat := 168202398435352102831025

theorem tailTrace_327573 : CollatzResearch.WordTrace tailWord_327573 prefixEnd_327573 168202398435352102831025 := by
  unfold tailWord_327573
  simp only [CollatzResearch.WordTrace]
  refine ⟨11947568842266440859499373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7965045894844293906332915 11947568842266440859499373)
  ·
    refine ⟨4480338315849915322312265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11947568842266440859499373 4480338315849915322312265)
    ·
      refine ⟨3360253736887436491734199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4480338315849915322312265 3360253736887436491734199)
      ·
        refine ⟨5040380605331154737601299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360253736887436491734199 5040380605331154737601299)
        ·
          refine ⟨7560570907996732106401949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5040380605331154737601299 7560570907996732106401949)
          ·
            refine ⟨2835214090498774539900731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7560570907996732106401949 2835214090498774539900731)
            ·
              refine ⟨4252821135748161809851097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2835214090498774539900731 4252821135748161809851097)
              ·
                refine ⟨3189615851811121357388323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4252821135748161809851097 3189615851811121357388323)
                ·
                  refine ⟨4784423777716682036082485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3189615851811121357388323 4784423777716682036082485)
                  ·
                    refine ⟨448539729160938940882733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4784423777716682036082485 448539729160938940882733)
                    ·
                      refine ⟨168202398435352102831025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 448539729160938940882733 168202398435352102831025)
                      ·
                        rfl

theorem cell23_327573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_327573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327573 prefixEnd_327573 := by exact prefixLift 327573
  have htrace : WordTrace (prefixWord ++ tailWord_327573) baseStart_327573 baseEnd_327573 := by
    simpa [prefixWord, tailWord_327573, baseEnd_327573] using wordTrace_append hprefix tailTrace_327573
  have hstable : (prefixWord ++ tailWord_327573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327573).length < 2 ^ (prefixWord ++ tailWord_327573).sum := by decide
  have hdescent : baseEnd_327573 < baseStart_327573 := by decide
  rcases family_descends (prefixWord ++ tailWord_327573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327591 : List Nat := [1, 1, 6, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_327591 : Nat := 118140960795 + 327591 * 2 ^ 59
def prefixEnd_327591 : Nat := 4983230072969 + 3 ^ 40 * 327591 * 2
def baseEnd_327591 : Nat := 168211641087133032405943

theorem tailTrace_327591 : CollatzResearch.WordTrace tailWord_327591 prefixEnd_327591 168211641087133032405943 := by
  unfold tailWord_327591
  simp only [CollatzResearch.WordTrace]
  refine ⟨11948225356201229933654627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7965483570800819955769751 11948225356201229933654627)
  ·
    refine ⟨17922338034301844900481941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11948225356201229933654627 17922338034301844900481941)
    ·
      refine ⟨840109595357898979710091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17922338034301844900481941 840109595357898979710091)
      ·
        refine ⟨1260164393036848469565137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840109595357898979710091 1260164393036848469565137)
        ·
          refine ⟨945123294777636352173853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1260164393036848469565137 945123294777636352173853)
          ·
            refine ⟨354421235541613632065195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 945123294777636352173853 354421235541613632065195)
            ·
              refine ⟨531631853312420448097793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354421235541613632065195 531631853312420448097793)
              ·
                refine ⟨398723889984315336073345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531631853312420448097793 398723889984315336073345)
                ·
                  refine ⟨299042917488236502055009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398723889984315336073345 299042917488236502055009)
                  ·
                    refine ⟨224282188116177376541257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299042917488236502055009 224282188116177376541257)
                    ·
                      refine ⟨168211641087133032405943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 224282188116177376541257 168211641087133032405943)
                      ·
                        rfl

theorem cell23_327591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_327591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327591 prefixEnd_327591 := by exact prefixLift 327591
  have htrace : WordTrace (prefixWord ++ tailWord_327591) baseStart_327591 baseEnd_327591 := by
    simpa [prefixWord, tailWord_327591, baseEnd_327591] using wordTrace_append hprefix tailTrace_327591
  have hstable : (prefixWord ++ tailWord_327591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327591).length < 2 ^ (prefixWord ++ tailWord_327591).sum := by decide
  have hdescent : baseEnd_327591 < baseStart_327591 := by decide
  rcases family_descends (prefixWord ++ tailWord_327591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327630 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_327630 : Nat := 118140960795 + 327630 * 2 ^ 59
def prefixEnd_327630 : Nat := 4983230072969 + 3 ^ 40 * 327630 * 2
def baseEnd_327630 : Nat := 168231666832658379818263

theorem tailTrace_327630 : CollatzResearch.WordTrace tailWord_327630 prefixEnd_327630 168231666832658379818263 := by
  unfold tailWord_327630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493705975382492449290543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7966431868706626396216229 1493705975382492449290543)
  ·
    refine ⟨2240558963073738673935815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1493705975382492449290543 2240558963073738673935815)
    ·
      refine ⟨3360838444610608010903723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240558963073738673935815 3360838444610608010903723)
      ·
        refine ⟨5041257666915912016355585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3360838444610608010903723 5041257666915912016355585)
        ·
          refine ⟨3780943250186934012266689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5041257666915912016355585 3780943250186934012266689)
          ·
            refine ⟨2835707437640200509200017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3780943250186934012266689 2835707437640200509200017)
            ·
              refine ⟨2126780578230150381900013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2835707437640200509200017 2126780578230150381900013)
              ·
                refine ⟨797542716836306393212505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2126780578230150381900013 797542716836306393212505)
                ·
                  refine ⟨598157037627229794909379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 797542716836306393212505 598157037627229794909379)
                  ·
                    refine ⟨897235556440844692364069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 598157037627229794909379 897235556440844692364069)
                    ·
                      refine ⟨168231666832658379818263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 897235556440844692364069 168231666832658379818263)
                      ·
                        rfl

theorem cell23_327630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_327630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327630 prefixEnd_327630 := by exact prefixLift 327630
  have htrace : WordTrace (prefixWord ++ tailWord_327630) baseStart_327630 baseEnd_327630 := by
    simpa [prefixWord, tailWord_327630, baseEnd_327630] using wordTrace_append hprefix tailTrace_327630
  have hstable : (prefixWord ++ tailWord_327630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327630).length < 2 ^ (prefixWord ++ tailWord_327630).sum := by decide
  have hdescent : baseEnd_327630 < baseStart_327630 := by decide
  rcases family_descends (prefixWord ++ tailWord_327630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327730 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_327730 : Nat := 118140960795 + 327730 * 2 ^ 59
def prefixEnd_327730 : Nat := 4983230072969 + 3 ^ 40 * 327730 * 2
def baseEnd_327730 : Nat := 56094338299369329522601

theorem tailTrace_327730 : CollatzResearch.WordTrace tailWord_327730 prefixEnd_327730 56094338299369329522601 := by
  unfold tailWord_327730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988323775674414168241161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7968863401798437781976429 2988323775674414168241161)
  ·
    refine ⟨2241242831755810626180871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2988323775674414168241161 2241242831755810626180871)
    ·
      refine ⟨3361864247633715939271307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2241242831755810626180871 3361864247633715939271307)
      ·
        refine ⟨5042796371450573908906961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3361864247633715939271307 5042796371450573908906961)
        ·
          refine ⟨3782097278587930431680221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5042796371450573908906961 3782097278587930431680221)
          ·
            refine ⟨1418286479470473911880083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3782097278587930431680221 1418286479470473911880083)
            ·
              refine ⟨2127429719205710867820125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418286479470473911880083 2127429719205710867820125)
              ·
                refine ⟨797786144702141575432547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2127429719205710867820125 797786144702141575432547)
                ·
                  refine ⟨1196679217053212363148821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797786144702141575432547 1196679217053212363148821)
                  ·
                    refine ⟨56094338299369329522601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1196679217053212363148821 56094338299369329522601)
                    ·
                      rfl

theorem cell23_327730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_327730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327730 prefixEnd_327730 := by exact prefixLift 327730
  have htrace : WordTrace (prefixWord ++ tailWord_327730) baseStart_327730 baseEnd_327730 := by
    simpa [prefixWord, tailWord_327730, baseEnd_327730] using wordTrace_append hprefix tailTrace_327730
  have hstable : (prefixWord ++ tailWord_327730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327730).length < 2 ^ (prefixWord ++ tailWord_327730).sum := by decide
  have hdescent : baseEnd_327730 < baseStart_327730 := by decide
  rcases family_descends (prefixWord ++ tailWord_327730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327743 : List Nat := [1, 1, 2, 2, 3, 1, 2, 11]
def baseStart_327743 : Nat := 118140960795 + 327743 * 2 ^ 59
def prefixEnd_327743 : Nat := 4983230072969 + 3 ^ 40 * 327743 * 2
def baseEnd_327743 : Nat := 6232951486911719915009

theorem tailTrace_327743 : CollatzResearch.WordTrace tailWord_327743 prefixEnd_327743 6232951486911719915009 := by
  unfold tailWord_327743
  simp only [CollatzResearch.WordTrace]
  refine ⟨11953769251650559893187883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7969179501100373262125255 11953769251650559893187883)
  ·
    refine ⟨17930653877475839839781825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11953769251650559893187883 17930653877475839839781825)
    ·
      refine ⟨13447990408106879879836369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17930653877475839839781825 13447990408106879879836369)
      ·
        refine ⟨10085992806080159909877277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13447990408106879879836369 10085992806080159909877277)
        ·
          refine ⟨3782247302280059966203979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10085992806080159909877277 3782247302280059966203979)
          ·
            refine ⟨5673370953420089949305969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3782247302280059966203979 5673370953420089949305969)
            ·
              refine ⟨4255028215065067461979477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5673370953420089949305969 4255028215065067461979477)
              ·
                refine ⟨6232951486911719915009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 4255028215065067461979477 6232951486911719915009)
                ·
                  rfl

theorem cell23_327743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 11].length) (baseStart_327743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327743 prefixEnd_327743 := by exact prefixLift 327743
  have htrace : WordTrace (prefixWord ++ tailWord_327743) baseStart_327743 baseEnd_327743 := by
    simpa [prefixWord, tailWord_327743, baseEnd_327743] using wordTrace_append hprefix tailTrace_327743
  have hstable : (prefixWord ++ tailWord_327743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327743).length < 2 ^ (prefixWord ++ tailWord_327743).sum := by decide
  have hdescent : baseEnd_327743 < baseStart_327743 := by decide
  rcases family_descends (prefixWord ++ tailWord_327743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327757 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_327757 : Nat := 118140960795 + 327757 * 2 ^ 59
def prefixEnd_327757 : Nat := 4983230072969 + 3 ^ 40 * 327757 * 2
def baseEnd_327757 : Nat := 168296878875779382930179

theorem tailTrace_327757 : CollatzResearch.WordTrace tailWord_327757 prefixEnd_327757 168296878875779382930179 := by
  unfold tailWord_327757
  simp only [CollatzResearch.WordTrace]
  refine ⟨11954279873599840284197525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7969519915733226856131683 11954279873599840284197525)
  ·
    refine ⟨560356869074992513321759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11954279873599840284197525 560356869074992513321759)
    ·
      refine ⟨840535303612488769982639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560356869074992513321759 840535303612488769982639)
      ·
        refine ⟨1260802955418733154973959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840535303612488769982639 1260802955418733154973959)
        ·
          refine ⟨1891204433128099732460939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260802955418733154973959 1891204433128099732460939)
          ·
            refine ⟨2836806649692149598691409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891204433128099732460939 2836806649692149598691409)
            ·
              refine ⟨2127604987269112199018557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2836806649692149598691409 2127604987269112199018557)
              ·
                refine ⟨797851870225917074631959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2127604987269112199018557 797851870225917074631959)
                ·
                  refine ⟨1196777805338875611947939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 797851870225917074631959 1196777805338875611947939)
                  ·
                    refine ⟨1795166708008313417921909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1196777805338875611947939 1795166708008313417921909)
                    ·
                      refine ⟨168296878875779382930179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1795166708008313417921909 168296878875779382930179)
                      ·
                        rfl

theorem cell23_327757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_327757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327757 prefixEnd_327757 := by exact prefixLift 327757
  have htrace : WordTrace (prefixWord ++ tailWord_327757) baseStart_327757 baseEnd_327757 := by
    simpa [prefixWord, tailWord_327757, baseEnd_327757] using wordTrace_append hprefix tailTrace_327757
  have hstable : (prefixWord ++ tailWord_327757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327757).length < 2 ^ (prefixWord ++ tailWord_327757).sum := by decide
  have hdescent : baseEnd_327757 < baseStart_327757 := by decide
  rcases family_descends (prefixWord ++ tailWord_327757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327838 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_327838 : Nat := 118140960795 + 327838 * 2 ^ 59
def prefixEnd_327838 : Nat := 4983230072969 + 3 ^ 40 * 327838 * 2
def baseEnd_327838 : Nat := 168338470808793566017307

theorem tailTrace_327838 : CollatzResearch.WordTrace tailWord_327838 prefixEnd_327838 168338470808793566017307 := by
  unfold tailWord_327838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1494654273288298889737021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7971489457537594078597445 1494654273288298889737021)
  ·
    refine ⟨560495352483112083651383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1494654273288298889737021 560495352483112083651383)
    ·
      refine ⟨840743028724668125477075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560495352483112083651383 840743028724668125477075)
      ·
        refine ⟨1261114543087002188215613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840743028724668125477075 1261114543087002188215613)
        ·
          refine ⟨472917953657625820580855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1261114543087002188215613 472917953657625820580855)
          ·
            refine ⟨709376930486438730871283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472917953657625820580855 709376930486438730871283)
            ·
              refine ⟨1064065395729658096306925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709376930486438730871283 1064065395729658096306925)
              ·
                refine ⟨399024523398621786115097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1064065395729658096306925 399024523398621786115097)
                ·
                  refine ⟨299268392548966339586323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399024523398621786115097 299268392548966339586323)
                  ·
                    refine ⟨448902588823449509379485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 299268392548966339586323 448902588823449509379485)
                    ·
                      refine ⟨168338470808793566017307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 448902588823449509379485 168338470808793566017307)
                      ·
                        rfl

theorem cell23_327838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_327838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327838 prefixEnd_327838 := by exact prefixLift 327838
  have htrace : WordTrace (prefixWord ++ tailWord_327838) baseStart_327838 baseEnd_327838 := by
    simpa [prefixWord, tailWord_327838, baseEnd_327838] using wordTrace_append hprefix tailTrace_327838
  have hstable : (prefixWord ++ tailWord_327838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327838).length < 2 ^ (prefixWord ++ tailWord_327838).sum := by decide
  have hdescent : baseEnd_327838 < baseStart_327838 := by decide
  rcases family_descends (prefixWord ++ tailWord_327838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327867 : List Nat := [1, 1, 1, 1, 1, 2, 6, 5, 5]
def baseStart_327867 : Nat := 118140960795 + 327867 * 2 ^ 59
def prefixEnd_327867 : Nat := 4983230072969 + 3 ^ 40 * 327867 * 2
def baseEnd_327867 : Nat := 18705929083085994728297

theorem tailTrace_327867 : CollatzResearch.WordTrace tailWord_327867 prefixEnd_327867 18705929083085994728297 := by
  unfold tailWord_327867
  simp only [CollatzResearch.WordTrace]
  refine ⟨11958291903201329070701855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7972194602134219380467903 11958291903201329070701855)
  ·
    refine ⟨17937437854801993606052783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11958291903201329070701855 17937437854801993606052783)
    ·
      refine ⟨26906156782202990409079175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17937437854801993606052783 26906156782202990409079175)
      ·
        refine ⟨40359235173304485613618763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26906156782202990409079175 40359235173304485613618763)
        ·
          refine ⟨60538852759956728420428145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40359235173304485613618763 60538852759956728420428145)
          ·
            refine ⟨45404139569967546315321109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60538852759956728420428145 45404139569967546315321109)
            ·
              refine ⟨2128319042342228733530677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45404139569967546315321109 2128319042342228733530677)
              ·
                refine ⟨199529910219583943768501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2128319042342228733530677 199529910219583943768501)
                ·
                  refine ⟨18705929083085994728297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199529910219583943768501 18705929083085994728297)
                  ·
                    rfl

theorem cell23_327867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 5].length) (baseStart_327867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327867 prefixEnd_327867 := by exact prefixLift 327867
  have htrace : WordTrace (prefixWord ++ tailWord_327867) baseStart_327867 baseEnd_327867 := by
    simpa [prefixWord, tailWord_327867, baseEnd_327867] using wordTrace_append hprefix tailTrace_327867
  have hstable : (prefixWord ++ tailWord_327867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327867).length < 2 ^ (prefixWord ++ tailWord_327867).sum := by decide
  have hdescent : baseEnd_327867 < baseStart_327867 := by decide
  rcases family_descends (prefixWord ++ tailWord_327867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327880 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 3, 7]
def baseStart_327880 : Nat := 118140960795 + 327880 * 2 ^ 59
def prefixEnd_327880 : Nat := 4983230072969 + 3 ^ 40 * 327880 * 2
def baseEnd_327880 : Nat := 56120012332094133897371

theorem tailTrace_327880 : CollatzResearch.WordTrace tailWord_327880 prefixEnd_327880 56120012332094133897371 := by
  unfold tailWord_327880
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979383026077116145462547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7972510701436154860616729 5979383026077116145462547)
  ·
    refine ⟨8969074539115674218193821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5979383026077116145462547 8969074539115674218193821)
    ·
      refine ⟨3363402952168377831822683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8969074539115674218193821 3363402952168377831822683)
      ·
        refine ⟨5045104428252566747734025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363402952168377831822683 5045104428252566747734025)
        ·
          refine ⟨3783828321189425060800519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5045104428252566747734025 3783828321189425060800519)
          ·
            refine ⟨5675742481784137591200779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783828321189425060800519 5675742481784137591200779)
            ·
              refine ⟨8513613722676206386801169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5675742481784137591200779 8513613722676206386801169)
              ·
                refine ⟨6385210292007154790100877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8513613722676206386801169 6385210292007154790100877)
                ·
                  refine ⟨2394453859502683046287829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6385210292007154790100877 2394453859502683046287829)
                  ·
                    refine ⟨56120012332094133897371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2394453859502683046287829 56120012332094133897371)
                    ·
                      rfl

theorem cell23_327880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_327880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327880 prefixEnd_327880 := by exact prefixLift 327880
  have htrace : WordTrace (prefixWord ++ tailWord_327880) baseStart_327880 baseEnd_327880 := by
    simpa [prefixWord, tailWord_327880, baseEnd_327880] using wordTrace_append hprefix tailTrace_327880
  have hstable : (prefixWord ++ tailWord_327880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327880).length < 2 ^ (prefixWord ++ tailWord_327880).sum := by decide
  have hdescent : baseEnd_327880 < baseStart_327880 := by decide
  rcases family_descends (prefixWord ++ tailWord_327880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327887 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 7, 2]
def baseStart_327887 : Nat := 118140960795 + 327887 * 2 ^ 59
def prefixEnd_327887 : Nat := 4983230072969 + 3 ^ 40 * 327887 * 2
def baseEnd_327887 : Nat := 168363631360863874304581

theorem tailTrace_327887 : CollatzResearch.WordTrace tailWord_327887 prefixEnd_327887 168363631360863874304581 := by
  unfold tailWord_327887
  simp only [CollatzResearch.WordTrace]
  refine ⟨11959021363128872486429915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7972680908752581657619943 11959021363128872486429915)
  ·
    refine ⟨17938532044693308729644873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11959021363128872486429915 17938532044693308729644873)
    ·
      refine ⟨13453899033519981547233655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17938532044693308729644873 13453899033519981547233655)
      ·
        refine ⟨20180848550279972320850483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13453899033519981547233655 20180848550279972320850483)
        ·
          refine ⟨30271272825419958481275725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20180848550279972320850483 30271272825419958481275725)
          ·
            refine ⟨11351727309532484430478397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30271272825419958481275725 11351727309532484430478397)
            ·
              refine ⟨4256897741074681661429399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11351727309532484430478397 4256897741074681661429399)
              ·
                refine ⟨6385346611612022492144099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4256897741074681661429399 6385346611612022492144099)
                ·
                  refine ⟨9578019917418033738216149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6385346611612022492144099 9578019917418033738216149)
                  ·
                    refine ⟨224484841814485165739441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9578019917418033738216149 224484841814485165739441)
                    ·
                      refine ⟨168363631360863874304581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 224484841814485165739441 168363631360863874304581)
                      ·
                        rfl

theorem cell23_327887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7, 2].length) (baseStart_327887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327887 prefixEnd_327887 := by exact prefixLift 327887
  have htrace : WordTrace (prefixWord ++ tailWord_327887) baseStart_327887 baseEnd_327887 := by
    simpa [prefixWord, tailWord_327887, baseEnd_327887] using wordTrace_append hprefix tailTrace_327887
  have hstable : (prefixWord ++ tailWord_327887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327887).length < 2 ^ (prefixWord ++ tailWord_327887).sum := by decide
  have hdescent : baseEnd_327887 < baseStart_327887 := by decide
  rcases family_descends (prefixWord ++ tailWord_327887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327934 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_327934 : Nat := 118140960795 + 327934 * 2 ^ 59
def prefixEnd_327934 : Nat := 4983230072969 + 3 ^ 40 * 327934 * 2
def baseEnd_327934 : Nat := 168387764951625190416865

theorem tailTrace_327934 : CollatzResearch.WordTrace tailWord_327934 prefixEnd_327934 168387764951625190416865 := by
  unfold tailWord_327934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495091949244824939173857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7973823729305733008927237 1495091949244824939173857)
  ·
    refine ⟨1121318961933618704380393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1495091949244824939173857 1121318961933618704380393)
    ·
      refine ⟨840989221450214028285295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1121318961933618704380393 840989221450214028285295)
      ·
        refine ⟨1261483832175321042427943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840989221450214028285295 1261483832175321042427943)
        ·
          refine ⟨1892225748262981563641915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261483832175321042427943 1892225748262981563641915)
          ·
            refine ⟨2838338622394472345462873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892225748262981563641915 2838338622394472345462873)
            ·
              refine ⟨2128753966795854259097155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2838338622394472345462873 2128753966795854259097155)
              ·
                refine ⟨3193130950193781388645733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2128753966795854259097155 3193130950193781388645733)
                ·
                  refine ⟨598712053161334010371075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3193130950193781388645733 598712053161334010371075)
                  ·
                    refine ⟨898068079742001015556613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 598712053161334010371075 898068079742001015556613)
                    ·
                      refine ⟨168387764951625190416865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 898068079742001015556613 168387764951625190416865)
                      ·
                        rfl

theorem cell23_327934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_327934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327934 prefixEnd_327934 := by exact prefixLift 327934
  have htrace : WordTrace (prefixWord ++ tailWord_327934) baseStart_327934 baseEnd_327934 := by
    simpa [prefixWord, tailWord_327934, baseEnd_327934] using wordTrace_append hprefix tailTrace_327934
  have hstable : (prefixWord ++ tailWord_327934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327934).length < 2 ^ (prefixWord ++ tailWord_327934).sum := by decide
  have hdescent : baseEnd_327934 < baseStart_327934 := by decide
  rcases family_descends (prefixWord ++ tailWord_327934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327944 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 3, 4]
def baseStart_327944 : Nat := 118140960795 + 327944 * 2 ^ 59
def prefixEnd_327944 : Nat := 4983230072969 + 3 ^ 40 * 327944 * 2
def baseEnd_327944 : Nat := 56130966586056717097273

theorem tailTrace_327944 : CollatzResearch.WordTrace tailWord_327944 prefixEnd_327944 56130966586056717097273 := by
  unfold tailWord_327944
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980550161961185610627443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7974066882614914147503257 5980550161961185610627443)
  ·
    refine ⟨8970825242941778415941165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5980550161961185610627443 8970825242941778415941165)
    ·
      refine ⟨3364059466103166905977937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8970825242941778415941165 3364059466103166905977937)
      ·
        refine ⟨2523044599577375179483453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3364059466103166905977937 2523044599577375179483453)
        ·
          refine ⟨946141724841515692306295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2523044599577375179483453 946141724841515692306295)
          ·
            refine ⟨1419212587262273538459443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946141724841515692306295 1419212587262273538459443)
            ·
              refine ⟨2128818880893410307689165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419212587262273538459443 2128818880893410307689165)
              ·
                refine ⟨798307080335028865383437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2128818880893410307689165 798307080335028865383437)
                ·
                  refine ⟨299365155125635824518789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798307080335028865383437 299365155125635824518789)
                  ·
                    refine ⟨56130966586056717097273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 299365155125635824518789 56130966586056717097273)
                    ·
                      rfl

theorem cell23_327944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_327944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327944 prefixEnd_327944 := by exact prefixLift 327944
  have htrace : WordTrace (prefixWord ++ tailWord_327944) baseStart_327944 baseEnd_327944 := by
    simpa [prefixWord, tailWord_327944, baseEnd_327944] using wordTrace_append hprefix tailTrace_327944
  have hstable : (prefixWord ++ tailWord_327944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327944).length < 2 ^ (prefixWord ++ tailWord_327944).sum := by decide
  have hdescent : baseEnd_327944 < baseStart_327944 := by decide
  rcases family_descends (prefixWord ++ tailWord_327944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_327957 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 6]
def baseStart_327957 : Nat := 118140960795 + 327957 * 2 ^ 59
def prefixEnd_327957 : Nat := 4983230072969 + 3 ^ 40 * 327957 * 2
def baseEnd_327957 : Nat := 18711063889630955603251

theorem tailTrace_327957 : CollatzResearch.WordTrace tailWord_327957 prefixEnd_327957 18711063889630955603251 := by
  unfold tailWord_327957
  simp only [CollatzResearch.WordTrace]
  refine ⟨11961574472875274441478125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7974382981916849627652083 11961574472875274441478125)
  ·
    refine ⟨4485590427328227915554297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11961574472875274441478125 4485590427328227915554297)
    ·
      refine ⟨3364192820496170936665723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4485590427328227915554297 3364192820496170936665723)
      ·
        refine ⟨5046289230744256404998585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3364192820496170936665723 5046289230744256404998585)
        ·
          refine ⟨3784716923058192303748939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5046289230744256404998585 3784716923058192303748939)
          ·
            refine ⟨5677075384587288455623409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3784716923058192303748939 5677075384587288455623409)
            ·
              refine ⟨4257806538440466341717557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5677075384587288455623409 4257806538440466341717557)
              ·
                refine ⟨399169362978793719536021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4257806538440466341717557 399169362978793719536021)
                ·
                  refine ⟨18711063889630955603251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 399169362978793719536021 18711063889630955603251)
                  ·
                    rfl

theorem cell23_327957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_327957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_327957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_327957 prefixEnd_327957 := by exact prefixLift 327957
  have htrace : WordTrace (prefixWord ++ tailWord_327957) baseStart_327957 baseEnd_327957 := by
    simpa [prefixWord, tailWord_327957, baseEnd_327957] using wordTrace_append hprefix tailTrace_327957
  have hstable : (prefixWord ++ tailWord_327957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_327957).length < 2 ^ (prefixWord ++ tailWord_327957).sum := by decide
  have hdescent : baseEnd_327957 < baseStart_327957 := by decide
  rcases family_descends (prefixWord ++ tailWord_327957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328024 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_328024 : Nat := 118140960795 + 328024 * 2 ^ 59
def prefixEnd_328024 : Nat := 4983230072969 + 3 ^ 40 * 328024 * 2
def baseEnd_328024 : Nat := 168433978210529838291451

theorem tailTrace_328024 : CollatzResearch.WordTrace tailWord_328024 prefixEnd_328024 168433978210529838291451 := by
  unfold tailWord_328024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982009081816272442083563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7976012109088363256111417 5982009081816272442083563)
  ·
    refine ⟨8973013622724408663125345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5982009081816272442083563 8973013622724408663125345)
    ·
      refine ⟨6729760217043306497344009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8973013622724408663125345 6729760217043306497344009)
      ·
        refine ⟨5047320162782479873008007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6729760217043306497344009 5047320162782479873008007)
        ·
          refine ⟨7570980244173719809512011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5047320162782479873008007 7570980244173719809512011)
          ·
            refine ⟨11356470366260579714268017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7570980244173719809512011 11356470366260579714268017)
            ·
              refine ⟨8517352774695434785701013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11356470366260579714268017 8517352774695434785701013)
              ·
                refine ⟨399250911313848505579735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8517352774695434785701013 399250911313848505579735)
                ·
                  refine ⟨598876366970772758369603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399250911313848505579735 598876366970772758369603)
                  ·
                    refine ⟨898314550456159137554405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 598876366970772758369603 898314550456159137554405)
                    ·
                      refine ⟨168433978210529838291451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 898314550456159137554405 168433978210529838291451)
                      ·
                        rfl

theorem cell23_328024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_328024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328024 prefixEnd_328024 := by exact prefixLift 328024
  have htrace : WordTrace (prefixWord ++ tailWord_328024) baseStart_328024 baseEnd_328024 := by
    simpa [prefixWord, tailWord_328024, baseEnd_328024] using wordTrace_append hprefix tailTrace_328024
  have hstable : (prefixWord ++ tailWord_328024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328024).length < 2 ^ (prefixWord ++ tailWord_328024).sum := by decide
  have hdescent : baseEnd_328024 < baseStart_328024 := by decide
  rcases family_descends (prefixWord ++ tailWord_328024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328034 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_328034 : Nat := 118140960795 + 328034 * 2 ^ 59
def prefixEnd_328034 : Nat := 4983230072969 + 3 ^ 40 * 328034 * 2
def baseEnd_328034 : Nat := 56146371005691599722135

theorem tailTrace_328034 : CollatzResearch.WordTrace tailWord_328034 prefixEnd_328034 56146371005691599722135 := by
  unfold tailWord_328034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991095723399079148007789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7976255262397544394687437 2991095723399079148007789)
  ·
    refine ⟨1121660896274654680502921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2991095723399079148007789 1121660896274654680502921)
    ·
      refine ⟨841245672205991010377191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1121660896274654680502921 841245672205991010377191)
      ·
        refine ⟨1261868508308986515565787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841245672205991010377191 1261868508308986515565787)
        ·
          refine ⟨1892802762463479773348681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261868508308986515565787 1892802762463479773348681)
          ·
            refine ⟨1419602071847609830011511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1892802762463479773348681 1419602071847609830011511)
            ·
              refine ⟨2129403107771414745017267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419602071847609830011511 2129403107771414745017267)
              ·
                refine ⟨3194104661657122117525901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2129403107771414745017267 3194104661657122117525901)
                ·
                  refine ⟨1197789248121420794072213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3194104661657122117525901 1197789248121420794072213)
                  ·
                    refine ⟨56146371005691599722135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1197789248121420794072213 56146371005691599722135)
                    ·
                      rfl

theorem cell23_328034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_328034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328034 prefixEnd_328034 := by exact prefixLift 328034
  have htrace : WordTrace (prefixWord ++ tailWord_328034) baseStart_328034 baseEnd_328034 := by
    simpa [prefixWord, tailWord_328034, baseEnd_328034] using wordTrace_append hprefix tailTrace_328034
  have hstable : (prefixWord ++ tailWord_328034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328034).length < 2 ^ (prefixWord ++ tailWord_328034).sum := by decide
  have hdescent : baseEnd_328034 < baseStart_328034 := by decide
  rcases family_descends (prefixWord ++ tailWord_328034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328041 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 1, 1, 4]
def baseStart_328041 : Nat := 118140960795 + 328041 * 2 ^ 59
def prefixEnd_328041 : Nat := 4983230072969 + 3 ^ 40 * 328041 * 2
def baseEnd_328041 : Nat := 168442707381656271778873

theorem tailTrace_328041 : CollatzResearch.WordTrace tailWord_328041 prefixEnd_328041 168442707381656271778873 := by
  unfold tailWord_328041
  simp only [CollatzResearch.WordTrace]
  refine ⟨11964638204570956787535977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7976425469713971191690651 11964638204570956787535977)
  ·
    refine ⟨8973478653428217590651983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11964638204570956787535977 8973478653428217590651983)
    ·
      refine ⟨13460217980142326385977975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8973478653428217590651983 13460217980142326385977975)
      ·
        refine ⟨20190326970213489578966963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13460217980142326385977975 20190326970213489578966963)
        ·
          refine ⟨30285490455320234368450445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20190326970213489578966963 30285490455320234368450445)
          ·
            refine ⟨11357058920745087888168917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30285490455320234368450445 11357058920745087888168917)
            ·
              refine ⟨266181068454962997378959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11357058920745087888168917 266181068454962997378959)
              ·
                refine ⟨399271602682444496068439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266181068454962997378959 399271602682444496068439)
                ·
                  refine ⟨598907404023666744102659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399271602682444496068439 598907404023666744102659)
                  ·
                    refine ⟨898361106035500116153989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 598907404023666744102659 898361106035500116153989)
                    ·
                      refine ⟨168442707381656271778873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 898361106035500116153989 168442707381656271778873)
                      ·
                        rfl

theorem cell23_328041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 1, 4].length) (baseStart_328041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328041 prefixEnd_328041 := by exact prefixLift 328041
  have htrace : WordTrace (prefixWord ++ tailWord_328041) baseStart_328041 baseEnd_328041 := by
    simpa [prefixWord, tailWord_328041, baseEnd_328041] using wordTrace_append hprefix tailTrace_328041
  have hstable : (prefixWord ++ tailWord_328041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328041).length < 2 ^ (prefixWord ++ tailWord_328041).sum := by decide
  have hdescent : baseEnd_328041 < baseStart_328041 := by decide
  rcases family_descends (prefixWord ++ tailWord_328041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328086 : List Nat := [5, 3, 1, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_328086 : Nat := 118140960795 + 328086 * 2 ^ 59
def prefixEnd_328086 : Nat := 4983230072969 + 3 ^ 40 * 328086 * 2
def baseEnd_328086 : Nat := 168465814011108595716167

theorem tailTrace_328086 : CollatzResearch.WordTrace tailWord_328086 prefixEnd_328086 168465814011108595716167 := by
  unfold tailWord_328086
  simp only [CollatzResearch.WordTrace]
  refine ⟨747892468087995592057757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7977519659605286315282741 747892468087995592057757)
  ·
    refine ⟨280459675532998347021659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 747892468087995592057757 280459675532998347021659)
    ·
      refine ⟨420689513299497520532489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280459675532998347021659 420689513299497520532489)
      ·
        refine ⟨315517134974623140399367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420689513299497520532489 315517134974623140399367)
        ·
          refine ⟨473275702461934710599051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315517134974623140399367 473275702461934710599051)
          ·
            refine ⟨709913553692902065898577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473275702461934710599051 709913553692902065898577)
            ·
              refine ⟨532435165269676549423933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709913553692902065898577 532435165269676549423933)
              ·
                refine ⟨199663186976128706033975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 532435165269676549423933 199663186976128706033975)
                ·
                  refine ⟨299494780464193059050963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199663186976128706033975 299494780464193059050963)
                  ·
                    refine ⟨449242170696289588576445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 299494780464193059050963 449242170696289588576445)
                    ·
                      refine ⟨168465814011108595716167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449242170696289588576445 168465814011108595716167)
                      ·
                        rfl

theorem cell23_328086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_328086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328086 prefixEnd_328086 := by exact prefixLift 328086
  have htrace : WordTrace (prefixWord ++ tailWord_328086) baseStart_328086 baseEnd_328086 := by
    simpa [prefixWord, tailWord_328086, baseEnd_328086] using wordTrace_append hprefix tailTrace_328086
  have hstable : (prefixWord ++ tailWord_328086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328086).length < 2 ^ (prefixWord ++ tailWord_328086).sum := by decide
  have hdescent : baseEnd_328086 < baseStart_328086 := by decide
  rcases family_descends (prefixWord ++ tailWord_328086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328125 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_328125 : Nat := 118140960795 + 328125 * 2 ^ 59
def prefixEnd_328125 : Nat := 4983230072969 + 3 ^ 40 * 328125 * 2
def baseEnd_328125 : Nat := 168485839756633943128487

theorem tailTrace_328125 : CollatzResearch.WordTrace tailWord_328125 prefixEnd_328125 168485839756633943128487 := by
  unfold tailWord_328125
  simp only [CollatzResearch.WordTrace]
  refine ⟨11967701936266639133593829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7978467957511092755729219 11967701936266639133593829)
  ·
    refine ⟨2243944113049994837548843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11967701936266639133593829 2243944113049994837548843)
    ·
      refine ⟨3365916169574992256323265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243944113049994837548843 3365916169574992256323265)
      ·
        refine ⟨2524437127181244192242449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3365916169574992256323265 2524437127181244192242449)
        ·
          refine ⟨1893327845385933144181837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2524437127181244192242449 1893327845385933144181837)
          ·
            refine ⟨709997942019724929068189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1893327845385933144181837 709997942019724929068189)
            ·
              refine ⟨266249228257396848400571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 709997942019724929068189 266249228257396848400571)
              ·
                refine ⟨399373842386095272600857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266249228257396848400571 399373842386095272600857)
                ·
                  refine ⟨299530381789571454450643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399373842386095272600857 299530381789571454450643)
                  ·
                    refine ⟨449295572684357181675965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 299530381789571454450643 449295572684357181675965)
                    ·
                      refine ⟨168485839756633943128487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449295572684357181675965 168485839756633943128487)
                      ·
                        rfl

theorem cell23_328125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_328125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328125 prefixEnd_328125 := by exact prefixLift 328125
  have htrace : WordTrace (prefixWord ++ tailWord_328125) baseStart_328125 baseEnd_328125 := by
    simpa [prefixWord, tailWord_328125, baseEnd_328125] using wordTrace_append hprefix tailTrace_328125
  have hstable : (prefixWord ++ tailWord_328125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328125).length < 2 ^ (prefixWord ++ tailWord_328125).sum := by decide
  have hdescent : baseEnd_328125 < baseStart_328125 := by decide
  rcases family_descends (prefixWord ++ tailWord_328125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328184 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 4, 5]
def baseStart_328184 : Nat := 118140960795 + 328184 * 2 ^ 59
def prefixEnd_328184 : Nat := 4983230072969 + 3 ^ 40 * 328184 * 2
def baseEnd_328184 : Nat := 56172045038416404096905

theorem tailTrace_328184 : CollatzResearch.WordTrace tailWord_328184 prefixEnd_328184 56172045038416404096905 := by
  unfold tailWord_328184
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984926921526446104995803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7979902562035261473327737 5984926921526446104995803)
  ·
    refine ⟨8977390382289669157493705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5984926921526446104995803 8977390382289669157493705)
    ·
      refine ⟨6733042786717251868120279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8977390382289669157493705 6733042786717251868120279)
      ·
        refine ⟨10099564180075877802180419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6733042786717251868120279 10099564180075877802180419)
        ·
          refine ⟨15149346270113816703270629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10099564180075877802180419 15149346270113816703270629)
          ·
            refine ⟨2840502425646340631863243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15149346270113816703270629 2840502425646340631863243)
            ·
              refine ⟨4260753638469510947794865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2840502425646340631863243 4260753638469510947794865)
              ·
                refine ⟨3195565228852133210846149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4260753638469510947794865 3195565228852133210846149)
                ·
                  refine ⟨599168480409774977033653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3195565228852133210846149 599168480409774977033653)
                  ·
                    refine ⟨56172045038416404096905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 599168480409774977033653 56172045038416404096905)
                    ·
                      rfl

theorem cell23_328184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_328184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328184 prefixEnd_328184 := by exact prefixLift 328184
  have htrace : WordTrace (prefixWord ++ tailWord_328184) baseStart_328184 baseEnd_328184 := by
    simpa [prefixWord, tailWord_328184, baseEnd_328184] using wordTrace_append hprefix tailTrace_328184
  have hstable : (prefixWord ++ tailWord_328184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328184).length < 2 ^ (prefixWord ++ tailWord_328184).sum := by decide
  have hdescent : baseEnd_328184 < baseStart_328184 := by decide
  rcases family_descends (prefixWord ++ tailWord_328184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328241 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_328241 : Nat := 118140960795 + 328241 * 2 ^ 59
def prefixEnd_328241 : Nat := 4983230072969 + 3 ^ 40 * 328241 * 2
def baseEnd_328241 : Nat := 168545403512555489277953

theorem tailTrace_328241 : CollatzResearch.WordTrace tailWord_328241 prefixEnd_328241 168545403512555489277953 := by
  unfold tailWord_328241
  simp only [CollatzResearch.WordTrace]
  refine ⟨11971932803846390944816577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7981288535897593963211051 11971932803846390944816577)
  ·
    refine ⟨8978949602884793208612433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11971932803846390944816577 8978949602884793208612433)
    ·
      refine ⟨6734212202163594906459325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8978949602884793208612433 6734212202163594906459325)
      ·
        refine ⟨2525329575811348089922247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6734212202163594906459325 2525329575811348089922247)
        ·
          refine ⟨3787994363717022134883371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525329575811348089922247 3787994363717022134883371)
          ·
            refine ⟨5681991545575533202325057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3787994363717022134883371 5681991545575533202325057)
            ·
              refine ⟨4261493659181649901743793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5681991545575533202325057 4261493659181649901743793)
              ·
                refine ⟨3196120244386237426307845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4261493659181649901743793 3196120244386237426307845)
                ·
                  refine ⟨599272545822419517432721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3196120244386237426307845 599272545822419517432721)
                  ·
                    refine ⟨449454409366814638074541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 599272545822419517432721 449454409366814638074541)
                    ·
                      refine ⟨168545403512555489277953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449454409366814638074541 168545403512555489277953)
                      ·
                        rfl

theorem cell23_328241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_328241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328241 prefixEnd_328241 := by exact prefixLift 328241
  have htrace : WordTrace (prefixWord ++ tailWord_328241) baseStart_328241 baseEnd_328241 := by
    simpa [prefixWord, tailWord_328241, baseEnd_328241] using wordTrace_append hprefix tailTrace_328241
  have hstable : (prefixWord ++ tailWord_328241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328241).length < 2 ^ (prefixWord ++ tailWord_328241).sum := by decide
  have hdescent : baseEnd_328241 < baseStart_328241 := by decide
  rcases family_descends (prefixWord ++ tailWord_328241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328264 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_328264 : Nat := 118140960795 + 328264 * 2 ^ 59
def prefixEnd_328264 : Nat := 4983230072969 + 3 ^ 40 * 328264 * 2
def baseEnd_328264 : Nat := 168557213567608899290347

theorem tailTrace_328264 : CollatzResearch.WordTrace tailWord_328264 prefixEnd_328264 168557213567608899290347 := by
  unfold tailWord_328264
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986385841381532936451923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7981847788508710581935897 5986385841381532936451923)
  ·
    refine ⟨8979578762072299404677885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5986385841381532936451923 8979578762072299404677885)
    ·
      refine ⟨3367342035777112276754207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8979578762072299404677885 3367342035777112276754207)
      ·
        refine ⟨5051013053665668415131311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3367342035777112276754207 5051013053665668415131311)
        ·
          refine ⟨7576519580498502622696967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5051013053665668415131311 7576519580498502622696967)
          ·
            refine ⟨11364779370747753934045451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7576519580498502622696967 11364779370747753934045451)
            ·
              refine ⟨17047169056121630901068177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11364779370747753934045451 17047169056121630901068177)
              ·
                refine ⟨12785376792091223175801133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17047169056121630901068177 12785376792091223175801133)
                ·
                  refine ⟨4794516297034208690925425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12785376792091223175801133 4794516297034208690925425)
                  ·
                    refine ⟨3595887222775656518194069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4794516297034208690925425 3595887222775656518194069)
                    ·
                      refine ⟨168557213567608899290347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3595887222775656518194069 168557213567608899290347)
                      ·
                        rfl

theorem cell23_328264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_328264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328264 prefixEnd_328264 := by exact prefixLift 328264
  have htrace : WordTrace (prefixWord ++ tailWord_328264) baseStart_328264 baseEnd_328264 := by
    simpa [prefixWord, tailWord_328264, baseEnd_328264] using wordTrace_append hprefix tailTrace_328264
  have hstable : (prefixWord ++ tailWord_328264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328264).length < 2 ^ (prefixWord ++ tailWord_328264).sum := by decide
  have hdescent : baseEnd_328264 < baseStart_328264 := by decide
  rcases family_descends (prefixWord ++ tailWord_328264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328288 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 3, 1, 3]
def baseStart_328288 : Nat := 118140960795 + 328288 * 2 ^ 59
def prefixEnd_328288 : Nat := 4983230072969 + 3 ^ 40 * 328288 * 2
def baseEnd_328288 : Nat := 168569537103316805390237

theorem tailTrace_328288 : CollatzResearch.WordTrace tailWord_328288 prefixEnd_328288 168569537103316805390237 := by
  unfold tailWord_328288
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986823517338058985888759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7982431356450745314518345 5986823517338058985888759)
  ·
    refine ⟨8980235276007088478833139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5986823517338058985888759 8980235276007088478833139)
    ·
      refine ⟨13470352914010632718249709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8980235276007088478833139 13470352914010632718249709)
      ·
        refine ⟨5051382342753987269343641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13470352914010632718249709 5051382342753987269343641)
        ·
          refine ⟨3788536757065490452007731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5051382342753987269343641 3788536757065490452007731)
          ·
            refine ⟨5682805135598235678011597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3788536757065490452007731 5682805135598235678011597)
            ·
              refine ⟨2131051925849338379254349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5682805135598235678011597 2131051925849338379254349)
              ·
                refine ⟨799144472193501892220381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2131051925849338379254349 799144472193501892220381)
                ·
                  refine ⟨299679177072563209582643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799144472193501892220381 299679177072563209582643)
                  ·
                    refine ⟨449518765608844814373965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 299679177072563209582643 449518765608844814373965)
                    ·
                      refine ⟨168569537103316805390237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449518765608844814373965 168569537103316805390237)
                      ·
                        rfl

theorem cell23_328288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_328288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328288 prefixEnd_328288 := by exact prefixLift 328288
  have htrace : WordTrace (prefixWord ++ tailWord_328288) baseStart_328288 baseEnd_328288 := by
    simpa [prefixWord, tailWord_328288, baseEnd_328288] using wordTrace_append hprefix tailTrace_328288
  have hstable : (prefixWord ++ tailWord_328288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328288).length < 2 ^ (prefixWord ++ tailWord_328288).sum := by decide
  have hdescent : baseEnd_328288 < baseStart_328288 := by decide
  rcases family_descends (prefixWord ++ tailWord_328288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328298 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_328298 : Nat := 118140960795 + 328298 * 2 ^ 59
def prefixEnd_328298 : Nat := 4983230072969 + 3 ^ 40 * 328298 * 2
def baseEnd_328298 : Nat := 168574671909861766265191

theorem tailTrace_328298 : CollatzResearch.WordTrace tailWord_328298 prefixEnd_328298 168574671909861766265191 := by
  unfold tailWord_328298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2993502941159972419910387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7982674509759926453094365 2993502941159972419910387)
  ·
    refine ⟨4490254411739958629865581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2993502941159972419910387 4490254411739958629865581)
    ·
      refine ⟨1683845404402484486199593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4490254411739958629865581 1683845404402484486199593)
      ·
        refine ⟨1262884053301863364649695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683845404402484486199593 1262884053301863364649695)
        ·
          refine ⟨1894326079952795046974543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262884053301863364649695 1894326079952795046974543)
          ·
            refine ⟨2841489119929192570461815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894326079952795046974543 2841489119929192570461815)
            ·
              refine ⟨4262233679893788855692723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841489119929192570461815 4262233679893788855692723)
              ·
                refine ⟨6393350519840683283539085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262233679893788855692723 6393350519840683283539085)
                ·
                  refine ⟨2397506444940256231327157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6393350519840683283539085 2397506444940256231327157)
                  ·
                    refine ⟨224766229213149021686921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2397506444940256231327157 224766229213149021686921)
                    ·
                      refine ⟨168574671909861766265191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 224766229213149021686921 168574671909861766265191)
                      ·
                        rfl

theorem cell23_328298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_328298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328298 prefixEnd_328298 := by exact prefixLift 328298
  have htrace : WordTrace (prefixWord ++ tailWord_328298) baseStart_328298 baseEnd_328298 := by
    simpa [prefixWord, tailWord_328298, baseEnd_328298] using wordTrace_append hprefix tailTrace_328298
  have hstable : (prefixWord ++ tailWord_328298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328298).length < 2 ^ (prefixWord ++ tailWord_328298).sum := by decide
  have hdescent : baseEnd_328298 < baseStart_328298 := by decide
  rcases family_descends (prefixWord ++ tailWord_328298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328311 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_328311 : Nat := 118140960795 + 328311 * 2 ^ 59
def prefixEnd_328311 : Nat := 4983230072969 + 3 ^ 40 * 328311 * 2
def baseEnd_328311 : Nat := 168581347158370215402631

theorem tailTrace_328311 : CollatzResearch.WordTrace tailWord_328311 prefixEnd_328311 168581347158370215402631 := by
  unfold tailWord_328311
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974485913592792899864787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7982990609061861933243191 11974485913592792899864787)
  ·
    refine ⟨17961728870389189349797181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11974485913592792899864787 17961728870389189349797181)
    ·
      refine ⟨6735648326395946006173943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17961728870389189349797181 6735648326395946006173943)
      ·
        refine ⟨10103472489593919009260915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6735648326395946006173943 10103472489593919009260915)
        ·
          refine ⟨15155208734390878513891373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10103472489593919009260915 15155208734390878513891373)
          ·
            refine ⟨5683203275396579442709265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15155208734390878513891373 5683203275396579442709265)
            ·
              refine ⟨4262402456547434582031949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5683203275396579442709265 4262402456547434582031949)
              ·
                refine ⟨1598400921205287968261981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4262402456547434582031949 1598400921205287968261981)
                ·
                  refine ⟨599400345451982988098243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1598400921205287968261981 599400345451982988098243)
                  ·
                    refine ⟨899100518177974482147365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 599400345451982988098243 899100518177974482147365)
                    ·
                      refine ⟨168581347158370215402631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 899100518177974482147365 168581347158370215402631)
                      ·
                        rfl

theorem cell23_328311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_328311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328311 prefixEnd_328311 := by exact prefixLift 328311
  have htrace : WordTrace (prefixWord ++ tailWord_328311) baseStart_328311 baseEnd_328311 := by
    simpa [prefixWord, tailWord_328311, baseEnd_328311] using wordTrace_append hprefix tailTrace_328311
  have hstable : (prefixWord ++ tailWord_328311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328311).length < 2 ^ (prefixWord ++ tailWord_328311).sum := by decide
  have hdescent : baseEnd_328311 < baseStart_328311 := by decide
  rcases family_descends (prefixWord ++ tailWord_328311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328321 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 3, 6]
def baseStart_328321 : Nat := 118140960795 + 328321 * 2 ^ 59
def prefixEnd_328321 : Nat := 4983230072969 + 3 ^ 40 * 328321 * 2
def baseEnd_328321 : Nat := 56195493988305058759195

theorem tailTrace_328321 : CollatzResearch.WordTrace tailWord_328321 prefixEnd_328321 56195493988305058759195 := by
  unfold tailWord_328321
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974850643556564607728817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7983233762371043071819211 11974850643556564607728817)
  ·
    refine ⟨8981137982667423455796613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11974850643556564607728817 8981137982667423455796613)
    ·
      refine ⟨1683963371750141897961865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8981137982667423455796613 1683963371750141897961865)
      ·
        refine ⟨1262972528812606423471399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683963371750141897961865 1262972528812606423471399)
        ·
          refine ⟨1894458793218909635207099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262972528812606423471399 1894458793218909635207099)
          ·
            refine ⟨2841688189828364452810649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894458793218909635207099 2841688189828364452810649)
            ·
              refine ⟨2131266142371273339607987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841688189828364452810649 2131266142371273339607987)
              ·
                refine ⟨3196899213556910009411981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131266142371273339607987 3196899213556910009411981)
                ·
                  refine ⟨1198837205083841253529493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3196899213556910009411981 1198837205083841253529493)
                  ·
                    refine ⟨56195493988305058759195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1198837205083841253529493 56195493988305058759195)
                    ·
                      rfl

theorem cell23_328321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_328321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328321 prefixEnd_328321 := by exact prefixLift 328321
  have htrace : WordTrace (prefixWord ++ tailWord_328321) baseStart_328321 baseEnd_328321 := by
    simpa [prefixWord, tailWord_328321, baseEnd_328321] using wordTrace_append hprefix tailTrace_328321
  have hstable : (prefixWord ++ tailWord_328321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328321).length < 2 ^ (prefixWord ++ tailWord_328321).sum := by decide
  have hdescent : baseEnd_328321 < baseStart_328321 := by decide
  rcases family_descends (prefixWord ++ tailWord_328321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328348 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_328348 : Nat := 118140960795 + 328348 * 2 ^ 59
def prefixEnd_328348 : Nat := 4983230072969 + 3 ^ 40 * 328348 * 2
def baseEnd_328348 : Nat := 168600345942586570639961

theorem tailTrace_328348 : CollatzResearch.WordTrace tailWord_328348 prefixEnd_328348 168600345942586570639961 := by
  unfold tailWord_328348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5987917707229374109480849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7983890276305832145974465 5987917707229374109480849)
  ·
    refine ⟨4490938280422030582110637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5987917707229374109480849 4490938280422030582110637)
    ·
      refine ⟨1684101855158261468291489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4490938280422030582110637 1684101855158261468291489)
      ·
        refine ⟨1263076391368696101218617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684101855158261468291489 1263076391368696101218617)
        ·
          refine ⟨947307293526522075913963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263076391368696101218617 947307293526522075913963)
          ·
            refine ⟨1420960940289783113870945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947307293526522075913963 1420960940289783113870945)
            ·
              refine ⟨1065720705217337335403209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420960940289783113870945 1065720705217337335403209)
              ·
                refine ⟨799290528913003001552407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065720705217337335403209 799290528913003001552407)
                ·
                  refine ⟨1198935793369504502328611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799290528913003001552407 1198935793369504502328611)
                  ·
                    refine ⟨1798403690054256753492917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1198935793369504502328611 1798403690054256753492917)
                    ·
                      refine ⟨168600345942586570639961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1798403690054256753492917 168600345942586570639961)
                      ·
                        rfl

theorem cell23_328348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_328348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328348 prefixEnd_328348 := by exact prefixLift 328348
  have htrace : WordTrace (prefixWord ++ tailWord_328348) baseStart_328348 baseEnd_328348 := by
    simpa [prefixWord, tailWord_328348, baseEnd_328348] using wordTrace_append hprefix tailTrace_328348
  have hstable : (prefixWord ++ tailWord_328348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328348).length < 2 ^ (prefixWord ++ tailWord_328348).sum := by decide
  have hdescent : baseEnd_328348 < baseStart_328348 := by decide
  rcases family_descends (prefixWord ++ tailWord_328348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328359 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 1, 5]
def baseStart_328359 : Nat := 118140960795 + 328359 * 2 ^ 59
def prefixEnd_328359 : Nat := 4983230072969 + 3 ^ 40 * 328359 * 2
def baseEnd_328359 : Nat := 56201998076595342534137

theorem tailTrace_328359 : CollatzResearch.WordTrace tailWord_328359 prefixEnd_328359 56201998076595342534137 := by
  unfold tailWord_328359
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976236617418897097612131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7984157744945931398408087 11976236617418897097612131)
  ·
    refine ⟨17964354926128345646418197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11976236617418897097612131 17964354926128345646418197)
    ·
      refine ⟨842079137162266202175853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17964354926128345646418197 842079137162266202175853)
      ·
        refine ⟨315779676435849825815945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 842079137162266202175853 315779676435849825815945)
        ·
          refine ⟨236834757326887369361959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315779676435849825815945 236834757326887369361959)
          ·
            refine ⟨355252135990331054042939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236834757326887369361959 355252135990331054042939)
            ·
              refine ⟨532878203985496581064409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355252135990331054042939 532878203985496581064409)
              ·
                refine ⟨399658652989122435798307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532878203985496581064409 399658652989122435798307)
                ·
                  refine ⟨599487979483683653697461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399658652989122435798307 599487979483683653697461)
                  ·
                    refine ⟨56201998076595342534137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 599487979483683653697461 56201998076595342534137)
                    ·
                      rfl

theorem cell23_328359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_328359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328359 prefixEnd_328359 := by exact prefixLift 328359
  have htrace : WordTrace (prefixWord ++ tailWord_328359) baseStart_328359 baseEnd_328359 := by
    simpa [prefixWord, tailWord_328359, baseEnd_328359] using wordTrace_append hprefix tailTrace_328359
  have hstable : (prefixWord ++ tailWord_328359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328359).length < 2 ^ (prefixWord ++ tailWord_328359).sum := by decide
  have hdescent : baseEnd_328359 < baseStart_328359 := by decide
  rcases family_descends (prefixWord ++ tailWord_328359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328362 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_328362 : Nat := 118140960795 + 328362 * 2 ^ 59
def prefixEnd_328362 : Nat := 4983230072969 + 3 ^ 40 * 328362 * 2
def baseEnd_328362 : Nat := 168607534671749515864897

theorem tailTrace_328362 : CollatzResearch.WordTrace tailWord_328362 prefixEnd_328362 168607534671749515864897 := by
  unfold tailWord_328362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2994086509102007152492835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7984230690938685739980893 2994086509102007152492835)
  ·
    refine ⟨4491129763653010728739253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2994086509102007152492835 4491129763653010728739253)
    ·
      refine ⟨421043415342469755819305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4491129763653010728739253 421043415342469755819305)
      ·
        refine ⟨315782561506852316864479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421043415342469755819305 315782561506852316864479)
        ·
          refine ⟨473673842260278475296719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315782561506852316864479 473673842260278475296719)
          ·
            refine ⟨710510763390417712945079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473673842260278475296719 710510763390417712945079)
            ·
              refine ⟨1065766145085626569417619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710510763390417712945079 1065766145085626569417619)
              ·
                refine ⟨1598649217628439854126429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065766145085626569417619 1598649217628439854126429)
                ·
                  refine ⟨599493456610664945297411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1598649217628439854126429 599493456610664945297411)
                  ·
                    refine ⟨899240184915997417946117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 599493456610664945297411 899240184915997417946117)
                    ·
                      refine ⟨168607534671749515864897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 899240184915997417946117 168607534671749515864897)
                      ·
                        rfl

theorem cell23_328362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_328362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328362 prefixEnd_328362 := by exact prefixLift 328362
  have htrace : WordTrace (prefixWord ++ tailWord_328362) baseStart_328362 baseEnd_328362 := by
    simpa [prefixWord, tailWord_328362, baseEnd_328362] using wordTrace_append hprefix tailTrace_328362
  have hstable : (prefixWord ++ tailWord_328362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328362).length < 2 ^ (prefixWord ++ tailWord_328362).sum := by decide
  have hdescent : baseEnd_328362 < baseStart_328362 := by decide
  rcases family_descends (prefixWord ++ tailWord_328362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328365 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_328365 : Nat := 118140960795 + 328365 * 2 ^ 59
def prefixEnd_328365 : Nat := 4983230072969 + 3 ^ 40 * 328365 * 2
def baseEnd_328365 : Nat := 168609075113713004127383

theorem tailTrace_328365 : CollatzResearch.WordTrace tailWord_328365 prefixEnd_328365 168609075113713004127383 := by
  unfold tailWord_328365
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976455455397160122330549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7984303636931440081553699 11976455455397160122330549)
  ·
    refine ⟨1122792698943483761468489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11976455455397160122330549 1122792698943483761468489)
    ·
      refine ⟨842094524207612821101367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1122792698943483761468489 842094524207612821101367)
      ·
        refine ⟨1263141786311419231652051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842094524207612821101367 1263141786311419231652051)
        ·
          refine ⟨1894712679467128847478077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263141786311419231652051 1894712679467128847478077)
          ·
            refine ⟨710517254800173317804279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1894712679467128847478077 710517254800173317804279)
            ·
              refine ⟨1065775882200259976706419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710517254800173317804279 1065775882200259976706419)
              ·
                refine ⟨1598663823300389965059629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065775882200259976706419 1598663823300389965059629)
                ·
                  refine ⟨599498933737646236897361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1598663823300389965059629 599498933737646236897361)
                  ·
                    refine ⟨449624200303234677673021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 599498933737646236897361 449624200303234677673021)
                    ·
                      refine ⟨168609075113713004127383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449624200303234677673021 168609075113713004127383)
                      ·
                        rfl

theorem cell23_328365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_328365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328365 prefixEnd_328365 := by exact prefixLift 328365
  have htrace : WordTrace (prefixWord ++ tailWord_328365) baseStart_328365 baseEnd_328365 := by
    simpa [prefixWord, tailWord_328365, baseEnd_328365] using wordTrace_append hprefix tailTrace_328365
  have hstable : (prefixWord ++ tailWord_328365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328365).length < 2 ^ (prefixWord ++ tailWord_328365).sum := by decide
  have hdescent : baseEnd_328365 < baseStart_328365 := by decide
  rcases family_descends (prefixWord ++ tailWord_328365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328378 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_328378 : Nat := 118140960795 + 328378 * 2 ^ 59
def prefixEnd_328378 : Nat := 4983230072969 + 3 ^ 40 * 328378 * 2
def baseEnd_328378 : Nat := 168615750362221453264823

theorem tailTrace_328378 : CollatzResearch.WordTrace tailWord_328378 prefixEnd_328378 168615750362221453264823 := by
  unfold tailWord_328378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2994232401087515835638447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7984619736233375561702525 2994232401087515835638447)
  ·
    refine ⟨4491348601631273753457671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2994232401087515835638447 4491348601631273753457671)
    ·
      refine ⟨6737022902446910630186507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4491348601631273753457671 6737022902446910630186507)
      ·
        refine ⟨10105534353670365945279761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737022902446910630186507 10105534353670365945279761)
        ·
          refine ⟨7579150765252774458959821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10105534353670365945279761 7579150765252774458959821)
          ·
            refine ⟨2842181536969790422109933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7579150765252774458959821 2842181536969790422109933)
            ·
              refine ⟨1065818076363671408291225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2842181536969790422109933 1065818076363671408291225)
              ·
                refine ⟨799363557272753556218419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065818076363671408291225 799363557272753556218419)
                ·
                  refine ⟨1199045335909130334327629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799363557272753556218419 1199045335909130334327629)
                  ·
                    refine ⟨449642000965923875372861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1199045335909130334327629 449642000965923875372861)
                    ·
                      refine ⟨168615750362221453264823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449642000965923875372861 168615750362221453264823)
                      ·
                        rfl

theorem cell23_328378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_328378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328378 prefixEnd_328378 := by exact prefixLift 328378
  have htrace : WordTrace (prefixWord ++ tailWord_328378) baseStart_328378 baseEnd_328378 := by
    simpa [prefixWord, tailWord_328378, baseEnd_328378] using wordTrace_append hprefix tailTrace_328378
  have hstable : (prefixWord ++ tailWord_328378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328378).length < 2 ^ (prefixWord ++ tailWord_328378).sum := by decide
  have hdescent : baseEnd_328378 < baseStart_328378 := by decide
  rcases family_descends (prefixWord ++ tailWord_328378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328382 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_328382 : Nat := 118140960795 + 328382 * 2 ^ 59
def prefixEnd_328382 : Nat := 4983230072969 + 3 ^ 40 * 328382 * 2
def baseEnd_328382 : Nat := 168617804284839437614805

theorem tailTrace_328382 : CollatzResearch.WordTrace tailWord_328382 prefixEnd_328382 168617804284839437614805 := by
  unfold tailWord_328382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497134437041946503212425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7984716997557048017132933 1497134437041946503212425)
  ·
    refine ⟨1122850827781459877409319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1497134437041946503212425 1122850827781459877409319)
    ·
      refine ⟨1684276241672189816113979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122850827781459877409319 1684276241672189816113979)
      ·
        refine ⟨2526414362508284724170969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684276241672189816113979 2526414362508284724170969)
        ·
          refine ⟨1894810771881213543128227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2526414362508284724170969 1894810771881213543128227)
          ·
            refine ⟨2842216157821820314692341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894810771881213543128227 2842216157821820314692341)
            ·
              refine ⟨266457764795795654502407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2842216157821820314692341 266457764795795654502407)
              ·
                refine ⟨399686647193693481753611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266457764795795654502407 399686647193693481753611)
                ·
                  refine ⟨599529970790540222630417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399686647193693481753611 599529970790540222630417)
                  ·
                    refine ⟨449647478092905166972813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 599529970790540222630417 449647478092905166972813)
                    ·
                      refine ⟨168617804284839437614805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449647478092905166972813 168617804284839437614805)
                      ·
                        rfl

theorem cell23_328382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_328382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328382 prefixEnd_328382 := by exact prefixLift 328382
  have htrace : WordTrace (prefixWord ++ tailWord_328382) baseStart_328382 baseEnd_328382 := by
    simpa [prefixWord, tailWord_328382, baseEnd_328382] using wordTrace_append hprefix tailTrace_328382
  have hstable : (prefixWord ++ tailWord_328382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328382).length < 2 ^ (prefixWord ++ tailWord_328382).sum := by decide
  have hdescent : baseEnd_328382 < baseStart_328382 := by decide
  rcases family_descends (prefixWord ++ tailWord_328382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328385 : List Nat := [1, 2, 6, 2, 2, 10]
def baseStart_328385 : Nat := 118140960795 + 328385 * 2 ^ 59
def prefixEnd_328385 : Nat := 4983230072969 + 3 ^ 40 * 328385 * 2
def baseEnd_328385 : Nat := 693906768423057308137

theorem tailTrace_328385 : CollatzResearch.WordTrace tailWord_328385 prefixEnd_328385 693906768423057308137 := by
  unfold tailWord_328385
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977184915324703538058609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7984789943549802358705739 11977184915324703538058609)
  ·
    refine ⟨8982888686493527653543957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11977184915324703538058609 8982888686493527653543957)
    ·
      refine ⟨421072907179384108759873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8982888686493527653543957 421072907179384108759873)
      ·
        refine ⟨315804680384538081569905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421072907179384108759873 315804680384538081569905)
        ·
          refine ⟨236853510288403561177429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315804680384538081569905 236853510288403561177429)
          ·
            refine ⟨693906768423057308137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 236853510288403561177429 693906768423057308137)
            ·
              rfl

theorem cell23_328385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 10].length) (baseStart_328385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328385 prefixEnd_328385 := by exact prefixLift 328385
  have htrace : WordTrace (prefixWord ++ tailWord_328385) baseStart_328385 baseEnd_328385 := by
    simpa [prefixWord, tailWord_328385, baseEnd_328385] using wordTrace_append hprefix tailTrace_328385
  have hstable : (prefixWord ++ tailWord_328385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328385).length < 2 ^ (prefixWord ++ tailWord_328385).sum := by decide
  have hdescent : baseEnd_328385 < baseStart_328385 := by decide
  rcases family_descends (prefixWord ++ tailWord_328385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328390 : List Nat := [6, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_328390 : Nat := 118140960795 + 328390 * 2 ^ 59
def prefixEnd_328390 : Nat := 4983230072969 + 3 ^ 40 * 328390 * 2
def baseEnd_328390 : Nat := 168621912130075406314769

theorem tailTrace_328390 : CollatzResearch.WordTrace tailWord_328390 prefixEnd_328390 168621912130075406314769 := by
  unfold tailWord_328390
  simp only [CollatzResearch.WordTrace]
  refine ⟨374292727509580918499707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7984911520204392927993749 374292727509580918499707)
  ·
    refine ⟨561439091264371377749561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 374292727509580918499707 561439091264371377749561)
    ·
      refine ⟨421079318448278533312171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 561439091264371377749561 421079318448278533312171)
      ·
        refine ⟨631618977672417799968257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421079318448278533312171 631618977672417799968257)
        ·
          refine ⟨473714233254313349976193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631618977672417799968257 473714233254313349976193)
          ·
            refine ⟨355285674940735012482145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473714233254313349976193 355285674940735012482145)
            ·
              refine ⟨266464256205551259361609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355285674940735012482145 266464256205551259361609)
              ·
                refine ⟨199848192154163444521207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266464256205551259361609 199848192154163444521207)
                ·
                  refine ⟨299772288231245166781811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199848192154163444521207 299772288231245166781811)
                  ·
                    refine ⟨449658432346867750172717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 299772288231245166781811 449658432346867750172717)
                    ·
                      refine ⟨168621912130075406314769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449658432346867750172717 168621912130075406314769)
                      ·
                        rfl

theorem cell23_328390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_328390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328390 prefixEnd_328390 := by exact prefixLift 328390
  have htrace : WordTrace (prefixWord ++ tailWord_328390) baseStart_328390 baseEnd_328390 := by
    simpa [prefixWord, tailWord_328390, baseEnd_328390] using wordTrace_append hprefix tailTrace_328390
  have hstable : (prefixWord ++ tailWord_328390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328390).length < 2 ^ (prefixWord ++ tailWord_328390).sum := by decide
  have hdescent : baseEnd_328390 < baseStart_328390 := by decide
  rcases family_descends (prefixWord ++ tailWord_328390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328396 : List Nat := [2, 2, 1, 5, 1, 1, 4, 2, 1, 2, 2]
def baseStart_328396 : Nat := 118140960795 + 328396 * 2 ^ 59
def prefixEnd_328396 : Nat := 4983230072969 + 3 ^ 40 * 328396 * 2
def baseEnd_328396 : Nat := 168624993014002382839741

theorem tailTrace_328396 : CollatzResearch.WordTrace tailWord_328396 prefixEnd_328396 168624993014002382839741 := by
  unfold tailWord_328396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988793059142426208354521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7985057412189901611139361 5988793059142426208354521)
  ·
    refine ⟨4491594794356819656265891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5988793059142426208354521 4491594794356819656265891)
    ·
      refine ⟨6737392191535229484398837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4491594794356819656265891 6737392191535229484398837)
      ·
        refine ⟨631630517956427764162391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6737392191535229484398837 631630517956427764162391)
        ·
          refine ⟨947445776934641646243587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631630517956427764162391 947445776934641646243587)
          ·
            refine ⟨1421168665401962469365381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947445776934641646243587 1421168665401962469365381)
            ·
              refine ⟨266469124762867963006009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1421168665401962469365381 266469124762867963006009)
              ·
                refine ⟨199851843572150972254507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266469124762867963006009 199851843572150972254507)
                ·
                  refine ⟨299777765358226458381761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199851843572150972254507 299777765358226458381761)
                  ·
                    refine ⟨224833324018669843786321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299777765358226458381761 224833324018669843786321)
                    ·
                      refine ⟨168624993014002382839741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 224833324018669843786321 168624993014002382839741)
                      ·
                        rfl

theorem cell23_328396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_328396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328396 prefixEnd_328396 := by exact prefixLift 328396
  have htrace : WordTrace (prefixWord ++ tailWord_328396) baseStart_328396 baseEnd_328396 := by
    simpa [prefixWord, tailWord_328396, baseEnd_328396] using wordTrace_append hprefix tailTrace_328396
  have hstable : (prefixWord ++ tailWord_328396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328396).length < 2 ^ (prefixWord ++ tailWord_328396).sum := by decide
  have hdescent : baseEnd_328396 < baseStart_328396 := by decide
  rcases family_descends (prefixWord ++ tailWord_328396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328401 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_328401 : Nat := 118140960795 + 328401 * 2 ^ 59
def prefixEnd_328401 : Nat := 4983230072969 + 3 ^ 40 * 328401 * 2
def baseEnd_328401 : Nat := 168627560417274863277217

theorem tailTrace_328401 : CollatzResearch.WordTrace tailWord_328401 prefixEnd_328401 168627560417274863277217 := by
  unfold tailWord_328401
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977768483266738270641057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7985178988844492180427371 11977768483266738270641057)
  ·
    refine ⟨8983326362450053702980793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11977768483266738270641057 8983326362450053702980793)
    ·
      refine ⟨6737494771837540277235595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8983326362450053702980793 6737494771837540277235595)
      ·
        refine ⟨10106242157756310415853393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737494771837540277235595 10106242157756310415853393)
        ·
          refine ⟨7579681618317232811890045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10106242157756310415853393 7579681618317232811890045)
          ·
            refine ⟨2842380606868962304458767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7579681618317232811890045 2842380606868962304458767)
            ·
              refine ⟨4263570910303443456688151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842380606868962304458767 4263570910303443456688151)
              ·
                refine ⟨6395356365455165185032227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263570910303443456688151 6395356365455165185032227)
                ·
                  refine ⟨9593034548182747777548341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6395356365455165185032227 9593034548182747777548341)
                  ·
                    refine ⟨899346988892132604145157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9593034548182747777548341 899346988892132604145157)
                    ·
                      refine ⟨168627560417274863277217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 899346988892132604145157 168627560417274863277217)
                      ·
                        rfl

theorem cell23_328401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_328401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328401 prefixEnd_328401 := by exact prefixLift 328401
  have htrace : WordTrace (prefixWord ++ tailWord_328401) baseStart_328401 baseEnd_328401 := by
    simpa [prefixWord, tailWord_328401, baseEnd_328401] using wordTrace_append hprefix tailTrace_328401
  have hstable : (prefixWord ++ tailWord_328401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328401).length < 2 ^ (prefixWord ++ tailWord_328401).sum := by decide
  have hdescent : baseEnd_328401 < baseStart_328401 := by decide
  rcases family_descends (prefixWord ++ tailWord_328401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328412 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_328412 : Nat := 118140960795 + 328412 * 2 ^ 59
def prefixEnd_328412 : Nat := 4983230072969 + 3 ^ 40 * 328412 * 2
def baseEnd_328412 : Nat := 168633208704474320239667

theorem tailTrace_328412 : CollatzResearch.WordTrace tailWord_328412 prefixEnd_328412 168633208704474320239667 := by
  unfold tailWord_328412
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989084843113443574645745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7985446457484591432860993 5989084843113443574645745)
  ·
    refine ⟨4491813632335082680984309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5989084843113443574645745 4491813632335082680984309)
    ·
      refine ⟨421107528031414001342279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4491813632335082680984309 421107528031414001342279)
      ·
        refine ⟨631661292047121002013419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421107528031414001342279 631661292047121002013419)
        ·
          refine ⟨947491938070681503020129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631661292047121002013419 947491938070681503020129)
          ·
            refine ⟨710618953553011127265097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947491938070681503020129 710618953553011127265097)
            ·
              refine ⟨532964215164758345448823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710618953553011127265097 532964215164758345448823)
              ·
                refine ⟨799446322747137518173235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532964215164758345448823 799446322747137518173235)
                ·
                  refine ⟨1199169484120706277259853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799446322747137518173235 1199169484120706277259853)
                  ·
                    refine ⟨449688556545264853972445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1199169484120706277259853 449688556545264853972445)
                    ·
                      refine ⟨168633208704474320239667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449688556545264853972445 168633208704474320239667)
                      ·
                        rfl

theorem cell23_328412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_328412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328412 prefixEnd_328412 := by exact prefixLift 328412
  have htrace : WordTrace (prefixWord ++ tailWord_328412) baseStart_328412 baseEnd_328412 := by
    simpa [prefixWord, tailWord_328412, baseEnd_328412] using wordTrace_append hprefix tailTrace_328412
  have hstable : (prefixWord ++ tailWord_328412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328412).length < 2 ^ (prefixWord ++ tailWord_328412).sum := by decide
  have hdescent : baseEnd_328412 < baseStart_328412 := by decide
  rcases family_descends (prefixWord ++ tailWord_328412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328435 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 4, 2, 2]
def baseStart_328435 : Nat := 118140960795 + 328435 * 2 ^ 59
def prefixEnd_328435 : Nat := 4983230072969 + 3 ^ 40 * 328435 * 2
def baseEnd_328435 : Nat := 168645018759527730252061

theorem tailTrace_328435 : CollatzResearch.WordTrace tailWord_328435 prefixEnd_328435 168645018759527730252061 := by
  unfold tailWord_328435
  simp only [CollatzResearch.WordTrace]
  refine ⟨11979008565143562077378759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7986005710095708051585839 11979008565143562077378759)
  ·
    refine ⟨17968512847715343116068139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11979008565143562077378759 17968512847715343116068139)
    ·
      refine ⟨26952769271573014674102209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17968512847715343116068139 26952769271573014674102209)
      ·
        refine ⟨20214576953679761005576657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26952769271573014674102209 20214576953679761005576657)
        ·
          refine ⟨15160932715259820754182493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20214576953679761005576657 15160932715259820754182493)
          ·
            refine ⟨5685349768222432782818435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15160932715259820754182493 5685349768222432782818435)
            ·
              refine ⟨8528024652333649174227653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685349768222432782818435 8528024652333649174227653)
              ·
                refine ⟨1599004622312559220167685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8528024652333649174227653 1599004622312559220167685)
                ·
                  refine ⟨299813366683604853781441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599004622312559220167685 299813366683604853781441)
                  ·
                    refine ⟨224860025012703640336081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299813366683604853781441 224860025012703640336081)
                    ·
                      refine ⟨168645018759527730252061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 224860025012703640336081 168645018759527730252061)
                      ·
                        rfl

theorem cell23_328435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 2, 2].length) (baseStart_328435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328435 prefixEnd_328435 := by exact prefixLift 328435
  have htrace : WordTrace (prefixWord ++ tailWord_328435) baseStart_328435 baseEnd_328435 := by
    simpa [prefixWord, tailWord_328435, baseEnd_328435] using wordTrace_append hprefix tailTrace_328435
  have hstable : (prefixWord ++ tailWord_328435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328435).length < 2 ^ (prefixWord ++ tailWord_328435).sum := by decide
  have hdescent : baseEnd_328435 < baseStart_328435 := by decide
  rcases family_descends (prefixWord ++ tailWord_328435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328438 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_328438 : Nat := 118140960795 + 328438 * 2 ^ 59
def prefixEnd_328438 : Nat := 4983230072969 + 3 ^ 40 * 328438 * 2
def baseEnd_328438 : Nat := 168646559201491218514547

theorem tailTrace_328438 : CollatzResearch.WordTrace tailWord_328438 prefixEnd_328438 168646559201491218514547 := by
  unfold tailWord_328438
  simp only [CollatzResearch.WordTrace]
  refine ⟨748694874008293349358623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7986078656088462393158645 748694874008293349358623)
  ·
    refine ⟨1123042311012440024037935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748694874008293349358623 1123042311012440024037935)
    ·
      refine ⟨1684563466518660036056903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123042311012440024037935 1684563466518660036056903)
      ·
        refine ⟨2526845199777990054085355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684563466518660036056903 2526845199777990054085355)
        ·
          refine ⟨3790267799666985081128033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526845199777990054085355 3790267799666985081128033)
          ·
            refine ⟨2842700849750238810846025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3790267799666985081128033 2842700849750238810846025)
            ·
              refine ⟨2132025637312679108134519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2842700849750238810846025 2132025637312679108134519)
              ·
                refine ⟨3198038455969018662201779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132025637312679108134519 3198038455969018662201779)
                ·
                  refine ⟨4797057683953527993302669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198038455969018662201779 4797057683953527993302669)
                  ·
                    refine ⟨1798896631482572997488501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4797057683953527993302669 1798896631482572997488501)
                    ·
                      refine ⟨168646559201491218514547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1798896631482572997488501 168646559201491218514547)
                      ·
                        rfl

theorem cell23_328438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_328438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328438 prefixEnd_328438 := by exact prefixLift 328438
  have htrace : WordTrace (prefixWord ++ tailWord_328438) baseStart_328438 baseEnd_328438 := by
    simpa [prefixWord, tailWord_328438, baseEnd_328438] using wordTrace_append hprefix tailTrace_328438
  have hstable : (prefixWord ++ tailWord_328438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328438).length < 2 ^ (prefixWord ++ tailWord_328438).sum := by decide
  have hdescent : baseEnd_328438 < baseStart_328438 := by decide
  rcases family_descends (prefixWord ++ tailWord_328438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328452 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_328452 : Nat := 118140960795 + 328452 * 2 ^ 59
def prefixEnd_328452 : Nat := 4983230072969 + 3 ^ 40 * 328452 * 2
def baseEnd_328452 : Nat := 168653747930654163739483

theorem tailTrace_328452 : CollatzResearch.WordTrace tailWord_328452 prefixEnd_328452 168653747930654163739483 := by
  unfold tailWord_328452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989814303040986990373805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7986419070721315987165073 5989814303040986990373805)
  ·
    refine ⟨2246180363640370121390177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5989814303040986990373805 2246180363640370121390177)
    ·
      refine ⟨1684635272730277591042633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2246180363640370121390177 1684635272730277591042633)
      ·
        refine ⟨1263476454547708193281975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684635272730277591042633 1263476454547708193281975)
        ·
          refine ⟨1895214681821562289922963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263476454547708193281975 1895214681821562289922963)
          ·
            refine ⟨2842822022732343434884445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895214681821562289922963 2842822022732343434884445)
            ·
              refine ⟨1066058258524628788081667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2842822022732343434884445 1066058258524628788081667)
              ·
                refine ⟨1599087387786943182122501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066058258524628788081667 1599087387786943182122501)
                ·
                  refine ⟨299828885210051846647969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599087387786943182122501 299828885210051846647969)
                  ·
                    refine ⟨224871663907538884985977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299828885210051846647969 224871663907538884985977)
                    ·
                      refine ⟨168653747930654163739483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 224871663907538884985977 168653747930654163739483)
                      ·
                        rfl

theorem cell23_328452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_328452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328452 prefixEnd_328452 := by exact prefixLift 328452
  have htrace : WordTrace (prefixWord ++ tailWord_328452) baseStart_328452 baseEnd_328452 := by
    simpa [prefixWord, tailWord_328452, baseEnd_328452] using wordTrace_append hprefix tailTrace_328452
  have hstable : (prefixWord ++ tailWord_328452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328452).length < 2 ^ (prefixWord ++ tailWord_328452).sum := by decide
  have hdescent : baseEnd_328452 < baseStart_328452 := by decide
  rcases family_descends (prefixWord ++ tailWord_328452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328458 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 7]
def baseStart_328458 : Nat := 118140960795 + 328458 * 2 ^ 59
def prefixEnd_328458 : Nat := 4983230072969 + 3 ^ 40 * 328458 * 2
def baseEnd_328458 : Nat := 18739647646064571140495

theorem tailTrace_328458 : CollatzResearch.WordTrace tailWord_328458 prefixEnd_328458 18739647646064571140495 := by
  unfold tailWord_328458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2994961861015059251366507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7986564962706824670310685 2994961861015059251366507)
  ·
    refine ⟨4492442791522588877049761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2994961861015059251366507 4492442791522588877049761)
    ·
      refine ⟨3369332093641941657787321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4492442791522588877049761 3369332093641941657787321)
      ·
        refine ⟨2526999070231456243340491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369332093641941657787321 2526999070231456243340491)
        ·
          refine ⟨3790498605347184365010737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526999070231456243340491 3790498605347184365010737)
          ·
            refine ⟨2842873954010388273758053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3790498605347184365010737 2842873954010388273758053)
            ·
              refine ⟨533038866376947801329635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2842873954010388273758053 533038866376947801329635)
              ·
                refine ⟨799558299565421701994453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533038866376947801329635 799558299565421701994453)
                ·
                  refine ⟨18739647646064571140495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 799558299565421701994453 18739647646064571140495)
                  ·
                    rfl

theorem cell23_328458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_328458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328458 prefixEnd_328458 := by exact prefixLift 328458
  have htrace : WordTrace (prefixWord ++ tailWord_328458) baseStart_328458 baseEnd_328458 := by
    simpa [prefixWord, tailWord_328458, baseEnd_328458] using wordTrace_append hprefix tailTrace_328458
  have hstable : (prefixWord ++ tailWord_328458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328458).length < 2 ^ (prefixWord ++ tailWord_328458).sum := by decide
  have hdescent : baseEnd_328458 < baseStart_328458 := by decide
  rcases family_descends (prefixWord ++ tailWord_328458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328469 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_328469 : Nat := 118140960795 + 328469 * 2 ^ 59
def prefixEnd_328469 : Nat := 4983230072969 + 3 ^ 40 * 328469 * 2
def baseEnd_328469 : Nat := 168662477101780597226905

theorem tailTrace_328469 : CollatzResearch.WordTrace tailWord_328469 prefixEnd_328469 168662477101780597226905 := by
  unfold tailWord_328469
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980248647020385884116461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7986832431346923922744307 11980248647020385884116461)
  ·
    refine ⟨4492593242632644706543673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11980248647020385884116461 4492593242632644706543673)
    ·
      refine ⟨3369444931974483529907755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4492593242632644706543673 3369444931974483529907755)
      ·
        refine ⟨5054167397961725294861633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369444931974483529907755 5054167397961725294861633)
        ·
          refine ⟨3790625548471293971146225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5054167397961725294861633 3790625548471293971146225)
          ·
            refine ⟨2842969161353470478359669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3790625548471293971146225 2842969161353470478359669)
            ·
              refine ⟨266528358876887857346219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2842969161353470478359669 266528358876887857346219)
              ·
                refine ⟨399792538315331786019329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266528358876887857346219 399792538315331786019329)
                ·
                  refine ⟨299844403736498839514497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399792538315331786019329 299844403736498839514497)
                  ·
                    refine ⟨224883302802374129635873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 299844403736498839514497 224883302802374129635873)
                    ·
                      refine ⟨168662477101780597226905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 224883302802374129635873 168662477101780597226905)
                      ·
                        rfl

theorem cell23_328469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_328469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328469 prefixEnd_328469 := by exact prefixLift 328469
  have htrace : WordTrace (prefixWord ++ tailWord_328469) baseStart_328469 baseEnd_328469 := by
    simpa [prefixWord, tailWord_328469, baseEnd_328469] using wordTrace_append hprefix tailTrace_328469
  have hstable : (prefixWord ++ tailWord_328469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328469).length < 2 ^ (prefixWord ++ tailWord_328469).sum := by decide
  have hdescent : baseEnd_328469 < baseStart_328469 := by decide
  rcases family_descends (prefixWord ++ tailWord_328469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328488 : List Nat := [2, 1, 5, 1, 1, 1, 1, 3, 1, 7]
def baseStart_328488 : Nat := 118140960795 + 328488 * 2 ^ 59
def prefixEnd_328488 : Nat := 4983230072969 + 3 ^ 40 * 328488 * 2
def baseEnd_328488 : Nat := 56224077744738674296439

theorem tailTrace_328488 : CollatzResearch.WordTrace tailWord_328488 prefixEnd_328488 56224077744738674296439 := by
  unfold tailWord_328488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990470816975776064529059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7987294422634368086038745 5990470816975776064529059)
  ·
    refine ⟨8985706225463664096793589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5990470816975776064529059 8985706225463664096793589)
    ·
      refine ⟨842409958637218509074399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8985706225463664096793589 842409958637218509074399)
      ·
        refine ⟨1263614937955827763611599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842409958637218509074399 1263614937955827763611599)
        ·
          refine ⟨1895422406933741645417399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263614937955827763611599 1895422406933741645417399)
          ·
            refine ⟨2843133610400612468126099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895422406933741645417399 2843133610400612468126099)
            ·
              refine ⟨4264700415600918702189149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843133610400612468126099 4264700415600918702189149)
              ·
                refine ⟨1599262655850344513320931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4264700415600918702189149 1599262655850344513320931)
                ·
                  refine ⟨2398893983775516769981397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599262655850344513320931 2398893983775516769981397)
                  ·
                    refine ⟨56224077744738674296439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2398893983775516769981397 56224077744738674296439)
                    ·
                      rfl

theorem cell23_328488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_328488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328488 prefixEnd_328488 := by exact prefixLift 328488
  have htrace : WordTrace (prefixWord ++ tailWord_328488) baseStart_328488 baseEnd_328488 := by
    simpa [prefixWord, tailWord_328488, baseEnd_328488] using wordTrace_append hprefix tailTrace_328488
  have hstable : (prefixWord ++ tailWord_328488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328488).length < 2 ^ (prefixWord ++ tailWord_328488).sum := by decide
  have hdescent : baseEnd_328488 < baseStart_328488 := by decide
  rcases family_descends (prefixWord ++ tailWord_328488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328498 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_328498 : Nat := 118140960795 + 328498 * 2 ^ 59
def prefixEnd_328498 : Nat := 4983230072969 + 3 ^ 40 * 328498 * 2
def baseEnd_328498 : Nat := 168677368040760983764271

theorem tailTrace_328498 : CollatzResearch.WordTrace tailWord_328498 prefixEnd_328498 168677368040760983764271 := by
  unfold tailWord_328498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995326590978830959230537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7987537575943549224614765 2995326590978830959230537)
  ·
    refine ⟨2246494943234123219422903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2995326590978830959230537 2246494943234123219422903)
    ·
      refine ⟨3369742414851184829134355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246494943234123219422903 3369742414851184829134355)
      ·
        refine ⟨5054613622276777243701533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369742414851184829134355 5054613622276777243701533)
        ·
          refine ⟨1895480108353791466388075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5054613622276777243701533 1895480108353791466388075)
          ·
            refine ⟨2843220162530687199582113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895480108353791466388075 2843220162530687199582113)
            ·
              refine ⟨2132415121898015399686585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843220162530687199582113 2132415121898015399686585)
              ·
                refine ⟨1599311341423511549764939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132415121898015399686585 1599311341423511549764939)
                ·
                  refine ⟨2398967012135267324647409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599311341423511549764939 2398967012135267324647409)
                  ·
                    refine ⟨1799225259101450493485557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2398967012135267324647409 1799225259101450493485557)
                    ·
                      refine ⟨168677368040760983764271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1799225259101450493485557 168677368040760983764271)
                      ·
                        rfl

theorem cell23_328498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_328498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328498 prefixEnd_328498 := by exact prefixLift 328498
  have htrace : WordTrace (prefixWord ++ tailWord_328498) baseStart_328498 baseEnd_328498 := by
    simpa [prefixWord, tailWord_328498, baseEnd_328498] using wordTrace_append hprefix tailTrace_328498
  have hstable : (prefixWord ++ tailWord_328498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328498).length < 2 ^ (prefixWord ++ tailWord_328498).sum := by decide
  have hdescent : baseEnd_328498 < baseStart_328498 := by decide
  rcases family_descends (prefixWord ++ tailWord_328498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328509 : List Nat := [1, 4, 1, 4, 2, 1, 3, 2, 5]
def baseStart_328509 : Nat := 118140960795 + 328509 * 2 ^ 59
def prefixEnd_328509 : Nat := 4983230072969 + 3 ^ 40 * 328509 * 2
def baseEnd_328509 : Nat := 18742557369773382302969

theorem tailTrace_328509 : CollatzResearch.WordTrace tailWord_328509 prefixEnd_328509 18742557369773382302969 := by
  unfold tailWord_328509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11981707566875472715572581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7987805044583648477048387 11981707566875472715572581)
  ·
    refine ⟨2246570168789151134169859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11981707566875472715572581 2246570168789151134169859)
    ·
      refine ⟨3369855253183726701254789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246570168789151134169859 3369855253183726701254789)
      ·
        refine ⟨631847859971948756485273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3369855253183726701254789 631847859971948756485273)
        ·
          refine ⟨473885894978961567363955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631847859971948756485273 473885894978961567363955)
          ·
            refine ⟨710828842468442351045933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473885894978961567363955 710828842468442351045933)
            ·
              refine ⟨266560815925665881642225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 710828842468442351045933 266560815925665881642225)
              ·
                refine ⟨199920611944249411231669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266560815925665881642225 199920611944249411231669)
                ·
                  refine ⟨18742557369773382302969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199920611944249411231669 18742557369773382302969)
                  ·
                    rfl

theorem cell23_328509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_328509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328509 prefixEnd_328509 := by exact prefixLift 328509
  have htrace : WordTrace (prefixWord ++ tailWord_328509) baseStart_328509 baseEnd_328509 := by
    simpa [prefixWord, tailWord_328509, baseEnd_328509] using wordTrace_append hprefix tailTrace_328509
  have hstable : (prefixWord ++ tailWord_328509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328509).length < 2 ^ (prefixWord ++ tailWord_328509).sum := by decide
  have hdescent : baseEnd_328509 < baseStart_328509 := by decide
  rcases family_descends (prefixWord ++ tailWord_328509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328528 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3]
def baseStart_328528 : Nat := 118140960795 + 328528 * 2 ^ 59
def prefixEnd_328528 : Nat := 4983230072969 + 3 ^ 40 * 328528 * 2
def baseEnd_328528 : Nat := 168692772460395866389133

theorem tailTrace_328528 : CollatzResearch.WordTrace tailWord_328528 prefixEnd_328528 168692772460395866389133 := by
  unfold tailWord_328528
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991200276903319480257119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7988267035871092640342825 5991200276903319480257119)
  ·
    refine ⟨8986800415354979220385679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5991200276903319480257119 8986800415354979220385679)
    ·
      refine ⟨13480200623032468830578519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8986800415354979220385679 13480200623032468830578519)
      ·
        refine ⟨20220300934548703245867779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13480200623032468830578519 20220300934548703245867779)
        ·
          refine ⟨30330451401823054868801669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20220300934548703245867779 30330451401823054868801669)
          ·
            refine ⟨5686959637841822787900313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30330451401823054868801669 5686959637841822787900313)
            ·
              refine ⟨4265219728381367090925235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5686959637841822787900313 4265219728381367090925235)
              ·
                refine ⟨6397829592572050636387853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265219728381367090925235 6397829592572050636387853)
                ·
                  refine ⟨2399186097214518988645445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6397829592572050636387853 2399186097214518988645445)
                  ·
                    refine ⟨449847393227722310371021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2399186097214518988645445 449847393227722310371021)
                    ·
                      refine ⟨168692772460395866389133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 449847393227722310371021 168692772460395866389133)
                      ·
                        rfl

theorem cell23_328528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_328528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328528 prefixEnd_328528 := by exact prefixLift 328528
  have htrace : WordTrace (prefixWord ++ tailWord_328528) baseStart_328528 baseEnd_328528 := by
    simpa [prefixWord, tailWord_328528, baseEnd_328528] using wordTrace_append hprefix tailTrace_328528
  have hstable : (prefixWord ++ tailWord_328528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328528).length < 2 ^ (prefixWord ++ tailWord_328528).sum := by decide
  have hdescent : baseEnd_328528 < baseStart_328528 := by decide
  rcases family_descends (prefixWord ++ tailWord_328528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328565 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 6]
def baseStart_328565 : Nat := 118140960795 + 328565 * 2 ^ 59
def prefixEnd_328565 : Nat := 4983230072969 + 3 ^ 40 * 328565 * 2
def baseEnd_328565 : Nat := 18745752360512469069607

theorem tailTrace_328565 : CollatzResearch.WordTrace tailWord_328565 prefixEnd_328565 18745752360512469069607 := by
  unfold tailWord_328565
  simp only [CollatzResearch.WordTrace]
  refine ⟨11983750054672594279611149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7989166703115062853074099 11983750054672594279611149)
  ·
    refine ⟨4493906270502222854854181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11983750054672594279611149 4493906270502222854854181)
    ·
      refine ⟨842607425719166785285159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4493906270502222854854181 842607425719166785285159)
      ·
        refine ⟨1263911138578750177927739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842607425719166785285159 1263911138578750177927739)
        ·
          refine ⟨1895866707868125266891609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263911138578750177927739 1895866707868125266891609)
          ·
            refine ⟨1421900030901093950168707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895866707868125266891609 1421900030901093950168707)
            ·
              refine ⟨2132850046351640925253061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421900030901093950168707 2132850046351640925253061)
              ·
                refine ⟨399909383690932673484949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2132850046351640925253061 399909383690932673484949)
                ·
                  refine ⟨18745752360512469069607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 399909383690932673484949 18745752360512469069607)
                  ·
                    rfl

theorem cell23_328565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_328565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328565 prefixEnd_328565 := by exact prefixLift 328565
  have htrace : WordTrace (prefixWord ++ tailWord_328565) baseStart_328565 baseEnd_328565 := by
    simpa [prefixWord, tailWord_328565, baseEnd_328565] using wordTrace_append hprefix tailTrace_328565
  have hstable : (prefixWord ++ tailWord_328565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328565).length < 2 ^ (prefixWord ++ tailWord_328565).sum := by decide
  have hdescent : baseEnd_328565 < baseStart_328565 := by decide
  rcases family_descends (prefixWord ++ tailWord_328565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328569 : List Nat := [1, 2, 1, 3, 2, 3, 4, 2, 1, 4]
def baseStart_328569 : Nat := 118140960795 + 328569 * 2 ^ 59
def prefixEnd_328569 : Nat := 4983230072969 + 3 ^ 40 * 328569 * 2
def baseEnd_328569 : Nat := 56237941722410068658815

theorem tailTrace_328569 : CollatzResearch.WordTrace tailWord_328569 prefixEnd_328569 56237941722410068658815 := by
  unfold tailWord_328569
  simp only [CollatzResearch.WordTrace]
  refine ⟨11983895946658102962756761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7989263964438735308504507 11983895946658102962756761)
  ·
    refine ⟨8987921959993577222067571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11983895946658102962756761 8987921959993577222067571)
    ·
      refine ⟨13481882939990365833101357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8987921959993577222067571 13481882939990365833101357)
      ·
        refine ⟨5055706102496387187413009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13481882939990365833101357 5055706102496387187413009)
        ·
          refine ⟨3791779576872290390559757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5055706102496387187413009 3791779576872290390559757)
          ·
            refine ⟨1421917341327108896459909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3791779576872290390559757 1421917341327108896459909)
            ·
              refine ⟨266609501498832918086233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1421917341327108896459909 266609501498832918086233)
              ·
                refine ⟨199957126124124688564675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266609501498832918086233 199957126124124688564675)
                ·
                  refine ⟨299935689186187032847013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199957126124124688564675 299935689186187032847013)
                  ·
                    refine ⟨56237941722410068658815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 299935689186187032847013 56237941722410068658815)
                    ·
                      rfl

theorem cell23_328569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 1, 4].length) (baseStart_328569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328569 prefixEnd_328569 := by exact prefixLift 328569
  have htrace : WordTrace (prefixWord ++ tailWord_328569) baseStart_328569 baseEnd_328569 := by
    simpa [prefixWord, tailWord_328569, baseEnd_328569] using wordTrace_append hprefix tailTrace_328569
  have hstable : (prefixWord ++ tailWord_328569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328569).length < 2 ^ (prefixWord ++ tailWord_328569).sum := by decide
  have hdescent : baseEnd_328569 < baseStart_328569 := by decide
  rcases family_descends (prefixWord ++ tailWord_328569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328655 : List Nat := [1, 1, 2, 1, 1, 6, 4, 7]
def baseStart_328655 : Nat := 118140960795 + 328655 * 2 ^ 59
def prefixEnd_328655 : Nat := 4983230072969 + 3 ^ 40 * 328655 * 2
def baseEnd_328655 : Nat := 6250295722352476648187

theorem tailTrace_328655 : CollatzResearch.WordTrace tailWord_328655 prefixEnd_328655 6250295722352476648187 := by
  unfold tailWord_328655
  simp only [CollatzResearch.WordTrace]
  refine ⟨11987032624346539650387419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7991355082897693100258279 11987032624346539650387419)
  ·
    refine ⟨17980548936519809475581129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11987032624346539650387419 17980548936519809475581129)
    ·
      refine ⟨13485411702389857106685847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17980548936519809475581129 13485411702389857106685847)
      ·
        refine ⟨20228117553584785660028771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13485411702389857106685847 20228117553584785660028771)
        ·
          refine ⟨30342176330377178490043157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20228117553584785660028771 30342176330377178490043157)
          ·
            refine ⟨1422289515486430241720773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30342176330377178490043157 1422289515486430241720773)
            ·
              refine ⟨266679284153705670322645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1422289515486430241720773 266679284153705670322645)
              ·
                refine ⟨6250295722352476648187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 266679284153705670322645 6250295722352476648187)
                ·
                  rfl

theorem cell23_328655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 7].length) (baseStart_328655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328655 prefixEnd_328655 := by exact prefixLift 328655
  have htrace : WordTrace (prefixWord ++ tailWord_328655) baseStart_328655 baseEnd_328655 := by
    simpa [prefixWord, tailWord_328655, baseEnd_328655] using wordTrace_append hprefix tailTrace_328655
  have hstable : (prefixWord ++ tailWord_328655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328655).length < 2 ^ (prefixWord ++ tailWord_328655).sum := by decide
  have hdescent : baseEnd_328655 < baseStart_328655 := by decide
  rcases family_descends (prefixWord ++ tailWord_328655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328669 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_328669 : Nat := 118140960795 + 328669 * 2 ^ 59
def prefixEnd_328669 : Nat := 4983230072969 + 3 ^ 40 * 328669 * 2
def baseEnd_328669 : Nat := 168765173232679814725985

theorem tailTrace_328669 : CollatzResearch.WordTrace tailWord_328669 prefixEnd_328669 168765173232679814725985 := by
  unfold tailWord_328669
  simp only [CollatzResearch.WordTrace]
  refine ⟨11987543246295820041397061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7991695497530546694264707 11987543246295820041397061)
  ·
    refine ⟨2247664358680466257761949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11987543246295820041397061 2247664358680466257761949)
    ·
      refine ⟨842874134505174846660731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2247664358680466257761949 842874134505174846660731)
      ·
        refine ⟨1264311201757762269991097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842874134505174846660731 1264311201757762269991097)
        ·
          refine ⟨948233401318321702493323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264311201757762269991097 948233401318321702493323)
          ·
            refine ⟨1422350101977482553739985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948233401318321702493323 1422350101977482553739985)
            ·
              refine ⟨1066762576483111915304989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422350101977482553739985 1066762576483111915304989)
              ·
                refine ⟨400035966181166968239371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1066762576483111915304989 400035966181166968239371)
                ·
                  refine ⟨600053949271750452359057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400035966181166968239371 600053949271750452359057)
                  ·
                    refine ⟨450040461953812839269293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 600053949271750452359057 450040461953812839269293)
                    ·
                      refine ⟨168765173232679814725985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450040461953812839269293 168765173232679814725985)
                      ·
                        rfl

theorem cell23_328669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_328669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328669 prefixEnd_328669 := by exact prefixLift 328669
  have htrace : WordTrace (prefixWord ++ tailWord_328669) baseStart_328669 baseEnd_328669 := by
    simpa [prefixWord, tailWord_328669, baseEnd_328669] using wordTrace_append hprefix tailTrace_328669
  have hstable : (prefixWord ++ tailWord_328669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328669).length < 2 ^ (prefixWord ++ tailWord_328669).sum := by decide
  have hdescent : baseEnd_328669 < baseStart_328669 := by decide
  rcases family_descends (prefixWord ++ tailWord_328669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328756 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_328756 : Nat := 118140960795 + 328756 * 2 ^ 59
def prefixEnd_328756 : Nat := 4983230072969 + 3 ^ 40 * 328756 * 2
def baseEnd_328756 : Nat := 168809846049620974338085

theorem tailTrace_328756 : CollatzResearch.WordTrace tailWord_328756 prefixEnd_328756 168809846049620974338085 := by
  unfold tailWord_328756
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995358198490316949907061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7993810931320422599876081 5995358198490316949907061)
  ·
    refine ⟨562064831108467214053787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5995358198490316949907061 562064831108467214053787)
    ·
      refine ⟨843097246662700821080681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562064831108467214053787 843097246662700821080681)
      ·
        refine ⟨632322934997025615810511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 843097246662700821080681 632322934997025615810511)
        ·
          refine ⟨948484402495538423715767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632322934997025615810511 948484402495538423715767)
          ·
            refine ⟨1422726603743307635573651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948484402495538423715767 1422726603743307635573651)
            ·
              refine ⟨2134089905614961453360477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422726603743307635573651 2134089905614961453360477)
              ·
                refine ⟨800283714605610545010179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2134089905614961453360477 800283714605610545010179)
                ·
                  refine ⟨1200425571908415817515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800283714605610545010179 1200425571908415817515269)
                  ·
                    refine ⟨225079794732827965784113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1200425571908415817515269 225079794732827965784113)
                    ·
                      refine ⟨168809846049620974338085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225079794732827965784113 168809846049620974338085)
                      ·
                        rfl

theorem cell23_328756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_328756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328756 prefixEnd_328756 := by exact prefixLift 328756
  have htrace : WordTrace (prefixWord ++ tailWord_328756) baseStart_328756 baseEnd_328756 := by
    simpa [prefixWord, tailWord_328756, baseEnd_328756] using wordTrace_append hprefix tailTrace_328756
  have hstable : (prefixWord ++ tailWord_328756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328756).length < 2 ^ (prefixWord ++ tailWord_328756).sum := by decide
  have hdescent : baseEnd_328756 < baseStart_328756 := by decide
  rcases family_descends (prefixWord ++ tailWord_328756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328785 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_328785 : Nat := 118140960795 + 328785 * 2 ^ 59
def prefixEnd_328785 : Nat := 4983230072969 + 3 ^ 40 * 328785 * 2
def baseEnd_328785 : Nat := 168824736988601360875451

theorem tailTrace_328785 : CollatzResearch.WordTrace tailWord_328785 prefixEnd_328785 168824736988601360875451 := by
  unfold tailWord_328785
  simp only [CollatzResearch.WordTrace]
  refine ⟨11991774113875571852619809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7994516075917047901746539 11991774113875571852619809)
  ·
    refine ⟨8993830585406678889464857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11991774113875571852619809 8993830585406678889464857)
    ·
      refine ⟨6745372939055009167098643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8993830585406678889464857 6745372939055009167098643)
      ·
        refine ⟨10118059408582513750647965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6745372939055009167098643 10118059408582513750647965)
        ·
          refine ⟨3794272278218442656492987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10118059408582513750647965 3794272278218442656492987)
          ·
            refine ⟨5691408417327663984739481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794272278218442656492987 5691408417327663984739481)
            ·
              refine ⟨4268556312995747988554611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691408417327663984739481 4268556312995747988554611)
              ·
                refine ⟨6402834469493621982831917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268556312995747988554611 6402834469493621982831917)
                ·
                  refine ⟨2401062926060108243561969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6402834469493621982831917 2401062926060108243561969)
                  ·
                    refine ⟨1800797194545081182671477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2401062926060108243561969 1800797194545081182671477)
                    ·
                      refine ⟨168824736988601360875451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1800797194545081182671477 168824736988601360875451)
                      ·
                        rfl

theorem cell23_328785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_328785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328785 prefixEnd_328785 := by exact prefixLift 328785
  have htrace : WordTrace (prefixWord ++ tailWord_328785) baseStart_328785 baseEnd_328785 := by
    simpa [prefixWord, tailWord_328785, baseEnd_328785] using wordTrace_append hprefix tailTrace_328785
  have hstable : (prefixWord ++ tailWord_328785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328785).length < 2 ^ (prefixWord ++ tailWord_328785).sum := by decide
  have hdescent : baseEnd_328785 < baseStart_328785 := by decide
  rcases family_descends (prefixWord ++ tailWord_328785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328790 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_328790 : Nat := 118140960795 + 328790 * 2 ^ 59
def prefixEnd_328790 : Nat := 4983230072969 + 3 ^ 40 * 328790 * 2
def baseEnd_328790 : Nat := 168827304391873841312929

theorem tailTrace_328790 : CollatzResearch.WordTrace tailWord_328790 prefixEnd_328790 168827304391873841312929 := by
  unfold tailWord_328790
  simp only [CollatzResearch.WordTrace]
  refine ⟨749497279928591106659489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7994637652571638471034549 749497279928591106659489)
  ·
    refine ⟨562122959946443329994617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 749497279928591106659489 562122959946443329994617)
    ·
      refine ⟨421592219959832497495963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562122959946443329994617 421592219959832497495963)
      ·
        refine ⟨632388329939748746243945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421592219959832497495963 632388329939748746243945)
        ·
          refine ⟨474291247454811559682959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632388329939748746243945 474291247454811559682959)
          ·
            refine ⟨711436871182217339524439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474291247454811559682959 711436871182217339524439)
            ·
              refine ⟨1067155306773326009286659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711436871182217339524439 1067155306773326009286659)
              ·
                refine ⟨1600732960159989013929989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067155306773326009286659 1600732960159989013929989)
                ·
                  refine ⟨300137430029997940111873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600732960159989013929989 300137430029997940111873)
                  ·
                    refine ⟨225103072522498455083905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 300137430029997940111873 225103072522498455083905)
                    ·
                      refine ⟨168827304391873841312929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225103072522498455083905 168827304391873841312929)
                      ·
                        rfl

theorem cell23_328790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_328790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328790 prefixEnd_328790 := by exact prefixLift 328790
  have htrace : WordTrace (prefixWord ++ tailWord_328790) baseStart_328790 baseEnd_328790 := by
    simpa [prefixWord, tailWord_328790, baseEnd_328790] using wordTrace_append hprefix tailTrace_328790
  have hstable : (prefixWord ++ tailWord_328790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328790).length < 2 ^ (prefixWord ++ tailWord_328790).sum := by decide
  have hdescent : baseEnd_328790 < baseStart_328790 := by decide
  rcases family_descends (prefixWord ++ tailWord_328790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328822 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_328822 : Nat := 118140960795 + 328822 * 2 ^ 59
def prefixEnd_328822 : Nat := 4983230072969 + 3 ^ 40 * 328822 * 2
def baseEnd_328822 : Nat := 56281245257605905370927

theorem tailTrace_328822 : CollatzResearch.WordTrace tailWord_328822 prefixEnd_328822 56281245257605905370927 := by
  unfold tailWord_328822
  simp only [CollatzResearch.WordTrace]
  refine ⟨749570225921345448232295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7995415743161018114477813 749570225921345448232295)
  ·
    refine ⟨1124355338882018172348443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 749570225921345448232295 1124355338882018172348443)
    ·
      refine ⟨1686533008323027258522665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1124355338882018172348443 1686533008323027258522665)
      ·
        refine ⟨1264899756242270443891999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1686533008323027258522665 1264899756242270443891999)
        ·
          refine ⟨1897349634363405665837999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264899756242270443891999 1897349634363405665837999)
          ·
            refine ⟨2846024451545108498756999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897349634363405665837999 2846024451545108498756999)
            ·
              refine ⟨4269036677317662748135499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846024451545108498756999 4269036677317662748135499)
              ·
                refine ⟨6403555015976494122203249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269036677317662748135499 6403555015976494122203249)
                ·
                  refine ⟨4802666261982370591652437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6403555015976494122203249 4802666261982370591652437)
                  ·
                    refine ⟨56281245257605905370927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4802666261982370591652437 56281245257605905370927)
                    ·
                      rfl

theorem cell23_328822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_328822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328822 prefixEnd_328822 := by exact prefixLift 328822
  have htrace : WordTrace (prefixWord ++ tailWord_328822) baseStart_328822 baseEnd_328822 := by
    simpa [prefixWord, tailWord_328822, baseEnd_328822] using wordTrace_append hprefix tailTrace_328822
  have hstable : (prefixWord ++ tailWord_328822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328822).length < 2 ^ (prefixWord ++ tailWord_328822).sum := by decide
  have hdescent : baseEnd_328822 < baseStart_328822 := by decide
  rcases family_descends (prefixWord ++ tailWord_328822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328832 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3]
def baseStart_328832 : Nat := 118140960795 + 328832 * 2 ^ 59
def prefixEnd_328832 : Nat := 4983230072969 + 3 ^ 40 * 328832 * 2
def baseEnd_328832 : Nat := 168848870579362676987735

theorem tailTrace_328832 : CollatzResearch.WordTrace tailWord_328832 prefixEnd_328832 168848870579362676987735 := by
  unfold tailWord_328832
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996744172352649439790375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7995658896470199253053833 5996744172352649439790375)
  ·
    refine ⟨8995116258528974159685563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5996744172352649439790375 8995116258528974159685563)
    ·
      refine ⟨13492674387793461239528345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8995116258528974159685563 13492674387793461239528345)
      ·
        refine ⟨10119505790845095929646259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13492674387793461239528345 10119505790845095929646259)
        ·
          refine ⟨15179258686267643894469389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10119505790845095929646259 15179258686267643894469389)
          ·
            refine ⟨5692222007350366460426021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15179258686267643894469389 5692222007350366460426021)
            ·
              refine ⟨1067291626378193711329879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5692222007350366460426021 1067291626378193711329879)
              ·
                refine ⟨1600937439567290566994819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067291626378193711329879 1600937439567290566994819)
                ·
                  refine ⟨2401406159350935850492229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600937439567290566994819 2401406159350935850492229)
                  ·
                    refine ⟨450263654878300471967293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401406159350935850492229 450263654878300471967293)
                    ·
                      refine ⟨168848870579362676987735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450263654878300471967293 168848870579362676987735)
                      ·
                        rfl

theorem cell23_328832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_328832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328832 prefixEnd_328832 := by exact prefixLift 328832
  have htrace : WordTrace (prefixWord ++ tailWord_328832) baseStart_328832 baseEnd_328832 := by
    simpa [prefixWord, tailWord_328832, baseEnd_328832] using wordTrace_append hprefix tailTrace_328832
  have hstable : (prefixWord ++ tailWord_328832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328832).length < 2 ^ (prefixWord ++ tailWord_328832).sum := by decide
  have hdescent : baseEnd_328832 < baseStart_328832 := by decide
  rcases family_descends (prefixWord ++ tailWord_328832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328835 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 10]
def baseStart_328835 : Nat := 118140960795 + 328835 * 2 ^ 59
def prefixEnd_328835 : Nat := 4983230072969 + 3 ^ 40 * 328835 * 2
def baseEnd_328835 : Nat := 18761156780147351694469

theorem tailTrace_328835 : CollatzResearch.WordTrace tailWord_328835 prefixEnd_328835 18761156780147351694469 := by
  unfold tailWord_328835
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993597763694430391939959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7995731842462953594626639 11993597763694430391939959)
  ·
    refine ⟨17990396645541645587909939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11993597763694430391939959 17990396645541645587909939)
    ·
      refine ⟨26985594968312468381864909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17990396645541645587909939 26985594968312468381864909)
      ·
        refine ⟨10119598113117175643199341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26985594968312468381864909 10119598113117175643199341)
        ·
          refine ⟨3794849292418940866199753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10119598113117175643199341 3794849292418940866199753)
          ·
            refine ⟨2846136969314205649649815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3794849292418940866199753 2846136969314205649649815)
            ·
              refine ⟨4269205453971308474474723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846136969314205649649815 4269205453971308474474723)
              ·
                refine ⟨6403808180956962711712085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269205453971308474474723 6403808180956962711712085)
                ·
                  refine ⟨18761156780147351694469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6403808180956962711712085 18761156780147351694469)
                  ·
                    rfl

theorem cell23_328835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 10].length) (baseStart_328835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328835 prefixEnd_328835 := by exact prefixLift 328835
  have htrace : WordTrace (prefixWord ++ tailWord_328835) baseStart_328835 baseEnd_328835 := by
    simpa [prefixWord, tailWord_328835, baseEnd_328835] using wordTrace_append hprefix tailTrace_328835
  have hstable : (prefixWord ++ tailWord_328835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328835).length < 2 ^ (prefixWord ++ tailWord_328835).sum := by decide
  have hdescent : baseEnd_328835 < baseStart_328835 := by decide
  rcases family_descends (prefixWord ++ tailWord_328835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328856 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 3, 4]
def baseStart_328856 : Nat := 118140960795 + 328856 * 2 ^ 59
def prefixEnd_328856 : Nat := 4983230072969 + 3 ^ 40 * 328856 * 2
def baseEnd_328856 : Nat := 56287064705023527695875

theorem tailTrace_328856 : CollatzResearch.WordTrace tailWord_328856 prefixEnd_328856 56287064705023527695875 := by
  unfold tailWord_328856
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997181848309175489227211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7996242464412233985636281 5997181848309175489227211)
  ·
    refine ⟨8995772772463763233840817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5997181848309175489227211 8995772772463763233840817)
    ·
      refine ⟨6746829579347822425380613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8995772772463763233840817 6746829579347822425380613)
      ·
        refine ⟨1265030546127716704758865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6746829579347822425380613 1265030546127716704758865)
        ·
          refine ⟨948772909595787528569149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265030546127716704758865 948772909595787528569149)
          ·
            refine ⟨355789841098420323213431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 948772909595787528569149 355789841098420323213431)
            ·
              refine ⟨533684761647630484820147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355789841098420323213431 533684761647630484820147)
              ·
                refine ⟨800527142471445727230221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533684761647630484820147 800527142471445727230221)
                ·
                  refine ⟨300197678426792147711333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800527142471445727230221 300197678426792147711333)
                  ·
                    refine ⟨56287064705023527695875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 300197678426792147711333 56287064705023527695875)
                    ·
                      rfl

theorem cell23_328856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_328856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328856 prefixEnd_328856 := by exact prefixLift 328856
  have htrace : WordTrace (prefixWord ++ tailWord_328856) baseStart_328856 baseEnd_328856 := by
    simpa [prefixWord, tailWord_328856, baseEnd_328856] using wordTrace_append hprefix tailTrace_328856
  have hstable : (prefixWord ++ tailWord_328856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328856).length < 2 ^ (prefixWord ++ tailWord_328856).sum := by decide
  have hdescent : baseEnd_328856 < baseStart_328856 := by decide
  rcases family_descends (prefixWord ++ tailWord_328856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328869 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 6]
def baseStart_328869 : Nat := 118140960795 + 328869 * 2 ^ 59
def prefixEnd_328869 : Nat := 4983230072969 + 3 ^ 40 * 328869 * 2
def baseEnd_328869 : Nat := 18763096595953225802785

theorem tailTrace_328869 : CollatzResearch.WordTrace tailWord_328869 prefixEnd_328869 18763096595953225802785 := by
  unfold tailWord_328869
  simp only [CollatzResearch.WordTrace]
  refine ⟨11994837845571254198677661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7996558563714169465785107 11994837845571254198677661)
  ·
    refine ⟨4498064192089220324504123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11994837845571254198677661 4498064192089220324504123)
    ·
      refine ⟨6747096288133830486756185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4498064192089220324504123 6747096288133830486756185)
      ·
        refine ⟨5060322216100372865067139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6747096288133830486756185 5060322216100372865067139)
        ·
          refine ⟨7590483324150559297600709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5060322216100372865067139 7590483324150559297600709)
          ·
            refine ⟨1423215623278229868300133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7590483324150559297600709 1423215623278229868300133)
            ·
              refine ⟨266852929364668100306275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1423215623278229868300133 266852929364668100306275)
              ·
                refine ⟨400279394047002150459413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266852929364668100306275 400279394047002150459413)
                ·
                  refine ⟨18763096595953225802785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 400279394047002150459413 18763096595953225802785)
                  ·
                    rfl

theorem cell23_328869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_328869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328869 prefixEnd_328869 := by exact prefixLift 328869
  have htrace : WordTrace (prefixWord ++ tailWord_328869) baseStart_328869 baseEnd_328869 := by
    simpa [prefixWord, tailWord_328869, baseEnd_328869] using wordTrace_append hprefix tailTrace_328869
  have hstable : (prefixWord ++ tailWord_328869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328869).length < 2 ^ (prefixWord ++ tailWord_328869).sum := by decide
  have hdescent : baseEnd_328869 < baseStart_328869 := by decide
  rcases family_descends (prefixWord ++ tailWord_328869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328879 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 3]
def baseStart_328879 : Nat := 118140960795 + 328879 * 2 ^ 59
def prefixEnd_328879 : Nat := 4983230072969 + 3 ^ 40 * 328879 * 2
def baseEnd_328879 : Nat := 168873004170123993100019

theorem tailTrace_328879 : CollatzResearch.WordTrace tailWord_328879 prefixEnd_328879 168873004170123993100019 := by
  unfold tailWord_328879
  simp only [CollatzResearch.WordTrace]
  refine ⟨11995202575535025906541691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7996801717023350604361127 11995202575535025906541691)
  ·
    refine ⟨17992803863302538859812537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11995202575535025906541691 17992803863302538859812537)
    ·
      refine ⟨13494602897476904144859403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17992803863302538859812537 13494602897476904144859403)
      ·
        refine ⟨20241904346215356217289105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13494602897476904144859403 20241904346215356217289105)
        ·
          refine ⟨15181428259661517162966829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20241904346215356217289105 15181428259661517162966829)
          ·
            refine ⟨5693035597373068936112561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15181428259661517162966829 5693035597373068936112561)
            ·
              refine ⟨4269776698029801702084421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5693035597373068936112561 4269776698029801702084421)
              ·
                refine ⟨800583130880587819140829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4269776698029801702084421 800583130880587819140829)
                ·
                  refine ⟨300218674080220432177811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800583130880587819140829 300218674080220432177811)
                  ·
                    refine ⟨450328011120330648266717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300218674080220432177811 450328011120330648266717)
                    ·
                      refine ⟨168873004170123993100019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450328011120330648266717 168873004170123993100019)
                      ·
                        rfl

theorem cell23_328879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 3].length) (baseStart_328879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328879 prefixEnd_328879 := by exact prefixLift 328879
  have htrace : WordTrace (prefixWord ++ tailWord_328879) baseStart_328879 baseEnd_328879 := by
    simpa [prefixWord, tailWord_328879, baseEnd_328879] using wordTrace_append hprefix tailTrace_328879
  have hstable : (prefixWord ++ tailWord_328879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328879).length < 2 ^ (prefixWord ++ tailWord_328879).sum := by decide
  have hdescent : baseEnd_328879 < baseStart_328879 := by decide
  rcases family_descends (prefixWord ++ tailWord_328879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328906 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_328906 : Nat := 118140960795 + 328906 * 2 ^ 59
def prefixEnd_328906 : Nat := 4983230072969 + 3 ^ 40 * 328906 * 2
def baseEnd_328906 : Nat := 168886868147795387462395

theorem tailTrace_328906 : CollatzResearch.WordTrace tailWord_328906 prefixEnd_328906 168886868147795387462395 := by
  unfold tailWord_328906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999046836609302379443643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7997458230958139678516381 2999046836609302379443643)
  ·
    refine ⟨4498570254913953569165465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2999046836609302379443643 4498570254913953569165465)
    ·
      refine ⟨3373927691185465176874099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4498570254913953569165465 3373927691185465176874099)
      ·
        refine ⟨5060891536778197765311149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3373927691185465176874099 5060891536778197765311149)
        ·
          refine ⟨1897834326291824161991681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5060891536778197765311149 1897834326291824161991681)
          ·
            refine ⟨1423375744718868121493761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897834326291824161991681 1423375744718868121493761)
            ·
              refine ⟨1067531808539151091120321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423375744718868121493761 1067531808539151091120321)
              ·
                refine ⟨800648856404363318340241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067531808539151091120321 800648856404363318340241)
                ·
                  refine ⟨600486642303272488755181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800648856404363318340241 600486642303272488755181)
                  ·
                    refine ⟨225182490863727183283193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 600486642303272488755181 225182490863727183283193)
                    ·
                      refine ⟨168886868147795387462395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225182490863727183283193 168886868147795387462395)
                      ·
                        rfl

theorem cell23_328906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_328906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328906 prefixEnd_328906 := by exact prefixLift 328906
  have htrace : WordTrace (prefixWord ++ tailWord_328906) baseStart_328906 baseEnd_328906 := by
    simpa [prefixWord, tailWord_328906, baseEnd_328906] using wordTrace_append hprefix tailTrace_328906
  have hstable : (prefixWord ++ tailWord_328906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328906).length < 2 ^ (prefixWord ++ tailWord_328906).sum := by decide
  have hdescent : baseEnd_328906 < baseStart_328906 := by decide
  rcases family_descends (prefixWord ++ tailWord_328906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328922 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_328922 : Nat := 118140960795 + 328922 * 2 ^ 59
def prefixEnd_328922 : Nat := 4983230072969 + 3 ^ 40 * 328922 * 2
def baseEnd_328922 : Nat := 168895083838267324862321

theorem tailTrace_328922 : CollatzResearch.WordTrace tailWord_328922 prefixEnd_328922 168895083838267324862321 := by
  unfold tailWord_328922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999192728594811062589255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7997847276252829500238013 2999192728594811062589255)
  ·
    refine ⟨4498789092892216593883883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2999192728594811062589255 4498789092892216593883883)
    ·
      refine ⟨6748183639338324890825825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4498789092892216593883883 6748183639338324890825825)
      ·
        refine ⟨5061137729503743668119369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748183639338324890825825 5061137729503743668119369)
        ·
          refine ⟨3795853297127807751089527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5061137729503743668119369 3795853297127807751089527)
          ·
            refine ⟨5693779945691711626634291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795853297127807751089527 5693779945691711626634291)
            ·
              refine ⟨8540669918537567439951437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693779945691711626634291 8540669918537567439951437)
              ·
                refine ⟨3202751219451587789981789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8540669918537567439951437 3202751219451587789981789)
                ·
                  refine ⟨1201031707294345421243171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3202751219451587789981789 1201031707294345421243171)
                  ·
                    refine ⟨1801547560941518131864757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1201031707294345421243171 1801547560941518131864757)
                    ·
                      refine ⟨168895083838267324862321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1801547560941518131864757 168895083838267324862321)
                      ·
                        rfl

theorem cell23_328922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_328922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328922 prefixEnd_328922 := by exact prefixLift 328922
  have htrace : WordTrace (prefixWord ++ tailWord_328922) baseStart_328922 baseEnd_328922 := by
    simpa [prefixWord, tailWord_328922, baseEnd_328922] using wordTrace_append hprefix tailTrace_328922
  have hstable : (prefixWord ++ tailWord_328922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328922).length < 2 ^ (prefixWord ++ tailWord_328922).sum := by decide
  have hdescent : baseEnd_328922 < baseStart_328922 := by decide
  rcases family_descends (prefixWord ++ tailWord_328922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328929 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 1, 6]
def baseStart_328929 : Nat := 118140960795 + 328929 * 2 ^ 59
def prefixEnd_328929 : Nat := 4983230072969 + 3 ^ 40 * 328929 * 2
def baseEnd_328929 : Nat := 56299559400949599158263

theorem tailTrace_328929 : CollatzResearch.WordTrace tailWord_328929 prefixEnd_328929 56299559400949599158263 := by
  unfold tailWord_328929
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997026225353884445861841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7998017483569256297241227 11997026225353884445861841)
  ·
    refine ⟨8997769669015413334396381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11997026225353884445861841 8997769669015413334396381)
    ·
      refine ⟨3374163625880780000398643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8997769669015413334396381 3374163625880780000398643)
      ·
        refine ⟨5061245438821170000597965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374163625880780000398643 5061245438821170000597965)
        ·
          refine ⟨1897967039557938750224237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5061245438821170000597965 1897967039557938750224237)
          ·
            refine ⟨711737639834227031334089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1897967039557938750224237 711737639834227031334089)
            ·
              refine ⟨533803229875670273500567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711737639834227031334089 533803229875670273500567)
              ·
                refine ⟨800704844813505410250851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533803229875670273500567 800704844813505410250851)
                ·
                  refine ⟨1201057267220258115376277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800704844813505410250851 1201057267220258115376277)
                  ·
                    refine ⟨56299559400949599158263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1201057267220258115376277 56299559400949599158263)
                    ·
                      rfl

theorem cell23_328929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_328929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328929 prefixEnd_328929 := by exact prefixLift 328929
  have htrace : WordTrace (prefixWord ++ tailWord_328929) baseStart_328929 baseEnd_328929 := by
    simpa [prefixWord, tailWord_328929, baseEnd_328929] using wordTrace_append hprefix tailTrace_328929
  have hstable : (prefixWord ++ tailWord_328929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328929).length < 2 ^ (prefixWord ++ tailWord_328929).sum := by decide
  have hdescent : baseEnd_328929 < baseStart_328929 := by decide
  rcases family_descends (prefixWord ++ tailWord_328929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328932 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_328932 : Nat := 118140960795 + 328932 * 2 ^ 59
def prefixEnd_328932 : Nat := 4983230072969 + 3 ^ 40 * 328932 * 2
def baseEnd_328932 : Nat := 168900218644812285737275

theorem tailTrace_328932 : CollatzResearch.WordTrace tailWord_328932 prefixEnd_328932 168900218644812285737275 := by
  unfold tailWord_328932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5998567822171507979110525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7998090429562010638814033 5998567822171507979110525)
  ·
    refine ⟨2249462933314315492166447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5998567822171507979110525 2249462933314315492166447)
    ·
      refine ⟨3374194399971473238249671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2249462933314315492166447 3374194399971473238249671)
      ·
        refine ⟨5061291599957209857374507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374194399971473238249671 5061291599957209857374507)
        ·
          refine ⟨7591937399935814786061761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061291599957209857374507 7591937399935814786061761)
          ·
            refine ⟨5693953049951861089546321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7591937399935814786061761 5693953049951861089546321)
            ·
              refine ⟨4270464787463895817159741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5693953049951861089546321 4270464787463895817159741)
              ·
                refine ⟨1601424295298960931434903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4270464787463895817159741 1601424295298960931434903)
                ·
                  refine ⟨2402136442948441397152355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601424295298960931434903 2402136442948441397152355)
                  ·
                    refine ⟨3603204664422662095728533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402136442948441397152355 3603204664422662095728533)
                    ·
                      refine ⟨168900218644812285737275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3603204664422662095728533 168900218644812285737275)
                      ·
                        rfl

theorem cell23_328932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_328932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328932 prefixEnd_328932 := by exact prefixLift 328932
  have htrace : WordTrace (prefixWord ++ tailWord_328932) baseStart_328932 baseEnd_328932 := by
    simpa [prefixWord, tailWord_328932, baseEnd_328932] using wordTrace_append hprefix tailTrace_328932
  have hstable : (prefixWord ++ tailWord_328932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328932).length < 2 ^ (prefixWord ++ tailWord_328932).sum := by decide
  have hdescent : baseEnd_328932 < baseStart_328932 := by decide
  rcases family_descends (prefixWord ++ tailWord_328932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328939 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 3]
def baseStart_328939 : Nat := 118140960795 + 328939 * 2 ^ 59
def prefixEnd_328939 : Nat := 4983230072969 + 3 ^ 40 * 328939 * 2
def baseEnd_328939 : Nat := 168903813009393758349743

theorem tailTrace_328939 : CollatzResearch.WordTrace tailWord_328939 prefixEnd_328939 168903813009393758349743 := by
  unfold tailWord_328939
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997390955317656153725871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7998260636878437435817247 11997390955317656153725871)
  ·
    refine ⟨17996086432976484230588807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11997390955317656153725871 17996086432976484230588807)
    ·
      refine ⟨26994129649464726345883211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17996086432976484230588807 26994129649464726345883211)
      ·
        refine ⟨40491194474197089518824817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26994129649464726345883211 40491194474197089518824817)
        ·
          refine ⟨30368395855647817139118613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40491194474197089518824817 30368395855647817139118613)
          ·
            refine ⟨1423518555733491428396185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30368395855647817139118613 1423518555733491428396185)
            ·
              refine ⟨1067638916800118571297139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423518555733491428396185 1067638916800118571297139)
              ·
                refine ⟨1601458375200177856945709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067638916800118571297139 1601458375200177856945709)
                ·
                  refine ⟨600546890700066696354641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1601458375200177856945709 600546890700066696354641)
                  ·
                    refine ⟨450410168025050022265981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 600546890700066696354641 450410168025050022265981)
                    ·
                      refine ⟨168903813009393758349743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450410168025050022265981 168903813009393758349743)
                      ·
                        rfl

theorem cell23_328939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 3].length) (baseStart_328939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328939 prefixEnd_328939 := by exact prefixLift 328939
  have htrace : WordTrace (prefixWord ++ tailWord_328939) baseStart_328939 baseEnd_328939 := by
    simpa [prefixWord, tailWord_328939, baseEnd_328939] using wordTrace_append hprefix tailTrace_328939
  have hstable : (prefixWord ++ tailWord_328939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328939).length < 2 ^ (prefixWord ++ tailWord_328939).sum := by decide
  have hdescent : baseEnd_328939 < baseStart_328939 := by decide
  rcases family_descends (prefixWord ++ tailWord_328939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328942 : List Nat := [4, 1, 2, 1, 1, 1, 2, 11]
def baseStart_328942 : Nat := 118140960795 + 328942 * 2 ^ 59
def prefixEnd_328942 : Nat := 4983230072969 + 3 ^ 40 * 328942 * 2
def baseEnd_328942 : Nat := 6255753831531749874527

theorem tailTrace_328942 : CollatzResearch.WordTrace tailWord_328942 prefixEnd_328942 6255753831531749874527 := by
  unfold tailWord_328942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499687546788348458260635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7998333582871191777390053 1499687546788348458260635)
  ·
    refine ⟨2249531320182522687390953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1499687546788348458260635 2249531320182522687390953)
    ·
      refine ⟨1687148490136892015543215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2249531320182522687390953 1687148490136892015543215)
      ·
        refine ⟨2530722735205338023314823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687148490136892015543215 2530722735205338023314823)
        ·
          refine ⟨3796084102808007034972235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530722735205338023314823 3796084102808007034972235)
          ·
            refine ⟨5694126154212010552458353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796084102808007034972235 5694126154212010552458353)
            ·
              refine ⟨4270594615659007914343765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5694126154212010552458353 4270594615659007914343765)
              ·
                refine ⟨6255753831531749874527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 4270594615659007914343765 6255753831531749874527)
                ·
                  rfl

theorem cell23_328942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_328942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328942 prefixEnd_328942 := by exact prefixLift 328942
  have htrace : WordTrace (prefixWord ++ tailWord_328942) baseStart_328942 baseEnd_328942 := by
    simpa [prefixWord, tailWord_328942, baseEnd_328942] using wordTrace_append hprefix tailTrace_328942
  have hstable : (prefixWord ++ tailWord_328942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328942).length < 2 ^ (prefixWord ++ tailWord_328942).sum := by decide
  have hdescent : baseEnd_328942 < baseStart_328942 := by decide
  rcases family_descends (prefixWord ++ tailWord_328942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_328986 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_328986 : Nat := 118140960795 + 328986 * 2 ^ 59
def prefixEnd_328986 : Nat := 4983230072969 + 3 ^ 40 * 328986 * 2
def baseEnd_328986 : Nat := 168927946600155074462027

theorem tailTrace_328986 : CollatzResearch.WordTrace tailWord_328986 prefixEnd_328986 168927946600155074462027 := by
  unfold tailWord_328986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999776296536845795171703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7999403457431588787124541 2999776296536845795171703)
  ·
    refine ⟨4499664444805268692757555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2999776296536845795171703 4499664444805268692757555)
    ·
      refine ⟨6749496667207903039136333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499664444805268692757555 6749496667207903039136333)
      ·
        refine ⟨2531061250202963639676125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6749496667207903039136333 2531061250202963639676125)
        ·
          refine ⟨949147968826111364878547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2531061250202963639676125 949147968826111364878547)
          ·
            refine ⟨1423721953239167047317821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949147968826111364878547 1423721953239167047317821)
            ·
              refine ⟨533895732464687642744183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423721953239167047317821 533895732464687642744183)
              ·
                refine ⟨800843598697031464116275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533895732464687642744183 800843598697031464116275)
                ·
                  refine ⟨1201265398045547196174413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800843598697031464116275 1201265398045547196174413)
                  ·
                    refine ⟨450474524267080198565405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1201265398045547196174413 450474524267080198565405)
                    ·
                      refine ⟨168927946600155074462027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450474524267080198565405 168927946600155074462027)
                      ·
                        rfl

theorem cell23_328986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_328986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_328986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_328986 prefixEnd_328986 := by exact prefixLift 328986
  have htrace : WordTrace (prefixWord ++ tailWord_328986) baseStart_328986 baseEnd_328986 := by
    simpa [prefixWord, tailWord_328986, baseEnd_328986] using wordTrace_append hprefix tailTrace_328986
  have hstable : (prefixWord ++ tailWord_328986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_328986).length < 2 ^ (prefixWord ++ tailWord_328986).sum := by decide
  have hdescent : baseEnd_328986 < baseStart_328986 := by decide
  rcases family_descends (prefixWord ++ tailWord_328986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329013 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_329013 : Nat := 118140960795 + 329013 * 2 ^ 59
def prefixEnd_329013 : Nat := 4983230072969 + 3 ^ 40 * 329013 * 2
def baseEnd_329013 : Nat := 168941810577826468824403

theorem tailTrace_329013 : CollatzResearch.WordTrace tailWord_329013 prefixEnd_329013 168941810577826468824403 := by
  unfold tailWord_329013
  simp only [CollatzResearch.WordTrace]
  refine ⟨12000089957049566791919693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8000059971366377861279795 12000089957049566791919693)
  ·
    refine ⟨4500033733893587546969885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12000089957049566791919693 4500033733893587546969885)
    ·
      refine ⟨1687512650210095330113707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4500033733893587546969885 1687512650210095330113707)
      ·
        refine ⟨2531268975315142995170561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687512650210095330113707 2531268975315142995170561)
        ·
          refine ⟨1898451731486357246377921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2531268975315142995170561 1898451731486357246377921)
          ·
            refine ⟨1423838798614767934783441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898451731486357246377921 1423838798614767934783441)
            ·
              refine ⟨1067879098961075951087581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423838798614767934783441 1067879098961075951087581)
              ·
                refine ⟨400454662110403481657843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067879098961075951087581 400454662110403481657843)
                ·
                  refine ⟨600681993165605222486765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400454662110403481657843 600681993165605222486765)
                  ·
                    refine ⟨225255747437101958432537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 600681993165605222486765 225255747437101958432537)
                    ·
                      refine ⟨168941810577826468824403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225255747437101958432537 168941810577826468824403)
                      ·
                        rfl

theorem cell23_329013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_329013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329013 prefixEnd_329013 := by exact prefixLift 329013
  have htrace : WordTrace (prefixWord ++ tailWord_329013) baseStart_329013 baseEnd_329013 := by
    simpa [prefixWord, tailWord_329013, baseEnd_329013] using wordTrace_append hprefix tailTrace_329013
  have hstable : (prefixWord ++ tailWord_329013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329013).length < 2 ^ (prefixWord ++ tailWord_329013).sum := by decide
  have hdescent : baseEnd_329013 < baseStart_329013 := by decide
  rcases family_descends (prefixWord ++ tailWord_329013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329037 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_329037 : Nat := 118140960795 + 329037 * 2 ^ 59
def prefixEnd_329037 : Nat := 4983230072969 + 3 ^ 40 * 329037 * 2
def baseEnd_329037 : Nat := 168954134113534374924293

theorem tailTrace_329037 : CollatzResearch.WordTrace tailWord_329037 prefixEnd_329037 168954134113534374924293 := by
  unfold tailWord_329037
  simp only [CollatzResearch.WordTrace]
  refine ⟨12000965308962618890793365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8000643539308412593862243 12000965308962618890793365)
  ·
    refine ⟨562545248857622760505939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12000965308962618890793365 562545248857622760505939)
    ·
      refine ⟨843817873286434140758909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562545248857622760505939 843817873286434140758909)
      ·
        refine ⟨316431702482412802784591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 843817873286434140758909 316431702482412802784591)
        ·
          refine ⟨474647553723619204176887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316431702482412802784591 474647553723619204176887)
          ·
            refine ⟨711971330585428806265331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474647553723619204176887 711971330585428806265331)
            ·
              refine ⟨1067956995878143209397997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711971330585428806265331 1067956995878143209397997)
              ·
                refine ⟨400483873454303703524249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067956995878143209397997 400483873454303703524249)
                ·
                  refine ⟨300362905090727777643187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400483873454303703524249 300362905090727777643187)
                  ·
                    refine ⟨450544357636091666464781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300362905090727777643187 450544357636091666464781)
                    ·
                      refine ⟨168954134113534374924293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450544357636091666464781 168954134113534374924293)
                      ·
                        rfl

theorem cell23_329037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_329037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329037 prefixEnd_329037 := by exact prefixLift 329037
  have htrace : WordTrace (prefixWord ++ tailWord_329037) baseStart_329037 baseEnd_329037 := by
    simpa [prefixWord, tailWord_329037, baseEnd_329037] using wordTrace_append hprefix tailTrace_329037
  have hstable : (prefixWord ++ tailWord_329037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329037).length < 2 ^ (prefixWord ++ tailWord_329037).sum := by decide
  have hdescent : baseEnd_329037 < baseStart_329037 := by decide
  rcases family_descends (prefixWord ++ tailWord_329037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329043 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 2, 2, 2]
def baseStart_329043 : Nat := 118140960795 + 329043 * 2 ^ 59
def prefixEnd_329043 : Nat := 4983230072969 + 3 ^ 40 * 329043 * 2
def baseEnd_329043 : Nat := 168957214997461351449265

theorem tailTrace_329043 : CollatzResearch.WordTrace tailWord_329043 prefixEnd_329043 168957214997461351449265 := by
  unfold tailWord_329043
  simp only [CollatzResearch.WordTrace]
  refine ⟨12001184146940881915511783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8000789431293921277007855 12001184146940881915511783)
  ·
    refine ⟨18001776220411322873267675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12001184146940881915511783 18001776220411322873267675)
    ·
      refine ⟨27002664330616984309901513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18001776220411322873267675 27002664330616984309901513)
      ·
        refine ⟨20251998247962738232426135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27002664330616984309901513 20251998247962738232426135)
        ·
          refine ⟨30377997371944107348639203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20251998247962738232426135 30377997371944107348639203)
          ·
            refine ⟨45566996057916161022958805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30377997371944107348639203 45566996057916161022958805)
            ·
              refine ⟨1067976470107410023975597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45566996057916161022958805 1067976470107410023975597)
              ·
                refine ⟨400491176290278758990849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067976470107410023975597 400491176290278758990849)
                ·
                  refine ⟨300368382217709069243137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400491176290278758990849 300368382217709069243137)
                  ·
                    refine ⟨225276286663281801932353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 300368382217709069243137 225276286663281801932353)
                    ·
                      refine ⟨168957214997461351449265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225276286663281801932353 168957214997461351449265)
                      ·
                        rfl

theorem cell23_329043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 2, 2].length) (baseStart_329043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329043 prefixEnd_329043 := by exact prefixLift 329043
  have htrace : WordTrace (prefixWord ++ tailWord_329043) baseStart_329043 baseEnd_329043 := by
    simpa [prefixWord, tailWord_329043, baseEnd_329043] using wordTrace_append hprefix tailTrace_329043
  have hstable : (prefixWord ++ tailWord_329043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329043).length < 2 ^ (prefixWord ++ tailWord_329043).sum := by decide
  have hdescent : baseEnd_329043 < baseStart_329043 := by decide
  rcases family_descends (prefixWord ++ tailWord_329043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329077 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_329077 : Nat := 118140960795 + 329077 * 2 ^ 59
def prefixEnd_329077 : Nat := 4983230072969 + 3 ^ 40 * 329077 * 2
def baseEnd_329077 : Nat := 168974673339714218424109

theorem tailTrace_329077 : CollatzResearch.WordTrace tailWord_329077 prefixEnd_329077 168974673339714218424109 := by
  unfold tailWord_329077
  simp only [CollatzResearch.WordTrace]
  refine ⟨12002424228817705722249485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8001616152545137148166323 12002424228817705722249485)
  ·
    refine ⟨4500909085806639645843557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12002424228817705722249485 4500909085806639645843557)
    ·
      refine ⟨843920453588744933595667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4500909085806639645843557 843920453588744933595667)
      ·
        refine ⟨1265880680383117400393501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843920453588744933595667 1265880680383117400393501)
        ·
          refine ⟨474705255143669025147563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1265880680383117400393501 474705255143669025147563)
          ·
            refine ⟨712057882715503537721345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474705255143669025147563 712057882715503537721345)
            ·
              refine ⟨534043412036627653291009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712057882715503537721345 534043412036627653291009)
              ·
                refine ⟨400532559027470739968257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534043412036627653291009 400532559027470739968257)
                ·
                  refine ⟨300399419270603054976193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400532559027470739968257 300399419270603054976193)
                  ·
                    refine ⟨225299564452952291232145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 300399419270603054976193 225299564452952291232145)
                    ·
                      refine ⟨168974673339714218424109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225299564452952291232145 168974673339714218424109)
                      ·
                        rfl

theorem cell23_329077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_329077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329077 prefixEnd_329077 := by exact prefixLift 329077
  have htrace : WordTrace (prefixWord ++ tailWord_329077) baseStart_329077 baseEnd_329077 := by
    simpa [prefixWord, tailWord_329077, baseEnd_329077] using wordTrace_append hprefix tailTrace_329077
  have hstable : (prefixWord ++ tailWord_329077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329077).length < 2 ^ (prefixWord ++ tailWord_329077).sum := by decide
  have hdescent : baseEnd_329077 < baseStart_329077 := by decide
  rcases family_descends (prefixWord ++ tailWord_329077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329079 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 2, 5]
def baseStart_329079 : Nat := 118140960795 + 329079 * 2 ^ 59
def prefixEnd_329079 : Nat := 4983230072969 + 3 ^ 40 * 329079 * 2
def baseEnd_329079 : Nat := 56325233433674403533033

theorem tailTrace_329079 : CollatzResearch.WordTrace tailWord_329079 prefixEnd_329079 56325233433674403533033 := by
  unfold tailWord_329079
  simp only [CollatzResearch.WordTrace]
  refine ⟨12002497174810460063822291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8001664783206973375881527 12002497174810460063822291)
  ·
    refine ⟨18003745762215690095733437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12002497174810460063822291 18003745762215690095733437)
    ·
      refine ⟨6751404660830883785900039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18003745762215690095733437 6751404660830883785900039)
      ·
        refine ⟨10127106991246325678850059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6751404660830883785900039 10127106991246325678850059)
        ·
          refine ⟨15190660486869488518275089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10127106991246325678850059 15190660486869488518275089)
          ·
            refine ⟨11392995365152116388706317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15190660486869488518275089 11392995365152116388706317)
            ·
              refine ⟨4272373261932043645764869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11392995365152116388706317 4272373261932043645764869)
              ·
                refine ⟨801069986612258183580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4272373261932043645764869 801069986612258183580913)
                ·
                  refine ⟨600802489959193637685685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 801069986612258183580913 600802489959193637685685)
                  ·
                    refine ⟨56325233433674403533033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 600802489959193637685685 56325233433674403533033)
                    ·
                      rfl

theorem cell23_329079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_329079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329079 prefixEnd_329079 := by exact prefixLift 329079
  have htrace : WordTrace (prefixWord ++ tailWord_329079) baseStart_329079 baseEnd_329079 := by
    simpa [prefixWord, tailWord_329079, baseEnd_329079] using wordTrace_append hprefix tailTrace_329079
  have hstable : (prefixWord ++ tailWord_329079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329079).length < 2 ^ (prefixWord ++ tailWord_329079).sum := by decide
  have hdescent : baseEnd_329079 < baseStart_329079 := by decide
  rcases family_descends (prefixWord ++ tailWord_329079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329099 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4]
def baseStart_329099 : Nat := 118140960795 + 329099 * 2 ^ 59
def prefixEnd_329099 : Nat := 4983230072969 + 3 ^ 40 * 329099 * 2
def baseEnd_329099 : Nat := 168985969914113132349007

theorem tailTrace_329099 : CollatzResearch.WordTrace tailWord_329099 prefixEnd_329099 168985969914113132349007 := by
  unfold tailWord_329099
  simp only [CollatzResearch.WordTrace]
  refine ⟨12003226634738003479550351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8002151089825335653033567 12003226634738003479550351)
  ·
    refine ⟨18004839952107005219325527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12003226634738003479550351 18004839952107005219325527)
    ·
      refine ⟨27007259928160507828988291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18004839952107005219325527 27007259928160507828988291)
      ·
        refine ⟨40510889892240761743482437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27007259928160507828988291 40510889892240761743482437)
        ·
          refine ⟨7595791854795142826902957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40510889892240761743482437 7595791854795142826902957)
          ·
            refine ⟨2848421945548178560088609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7595791854795142826902957 2848421945548178560088609)
            ·
              refine ⟨2136316459161133920066457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848421945548178560088609 2136316459161133920066457)
              ·
                refine ⟨1602237344370850440049843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136316459161133920066457 1602237344370850440049843)
                ·
                  refine ⟨2403356016556275660074765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1602237344370850440049843 2403356016556275660074765)
                  ·
                    refine ⟨901258506208603372528037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403356016556275660074765 901258506208603372528037)
                    ·
                      refine ⟨168985969914113132349007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 901258506208603372528037 168985969914113132349007)
                      ·
                        rfl

theorem cell23_329099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_329099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329099 prefixEnd_329099 := by exact prefixLift 329099
  have htrace : WordTrace (prefixWord ++ tailWord_329099) baseStart_329099 baseEnd_329099 := by
    simpa [prefixWord, tailWord_329099, baseEnd_329099] using wordTrace_append hprefix tailTrace_329099
  have hstable : (prefixWord ++ tailWord_329099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329099).length < 2 ^ (prefixWord ++ tailWord_329099).sum := by decide
  have hdescent : baseEnd_329099 < baseStart_329099 := by decide
  rcases family_descends (prefixWord ++ tailWord_329099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329143 : List Nat := [1, 1, 3, 1, 3, 2, 1, 6, 1, 4]
def baseStart_329143 : Nat := 118140960795 + 329143 * 2 ^ 59
def prefixEnd_329143 : Nat := 4983230072969 + 3 ^ 40 * 329143 * 2
def baseEnd_329143 : Nat := 56336187687636986732935

theorem tailTrace_329143 : CollatzResearch.WordTrace tailWord_329143 prefixEnd_329143 56336187687636986732935 := by
  unfold tailWord_329143
  simp only [CollatzResearch.WordTrace]
  refine ⟨12004831446578598994152083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8003220964385732662768055 12004831446578598994152083)
  ·
    refine ⟨18007247169867898491228125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12004831446578598994152083 18007247169867898491228125)
    ·
      refine ⟨6752717688700461934210547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18007247169867898491228125 6752717688700461934210547)
      ·
        refine ⟨10129076533050692901315821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6752717688700461934210547 10129076533050692901315821)
        ·
          refine ⟨3798403699894009837993433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10129076533050692901315821 3798403699894009837993433)
          ·
            refine ⟨2848802774920507378495075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3798403699894009837993433 2848802774920507378495075)
            ·
              refine ⟨4273204162380761067742613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848802774920507378495075 4273204162380761067742613)
              ·
                refine ⟨200306445111598175050435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4273204162380761067742613 200306445111598175050435)
                ·
                  refine ⟨300459667667397262575653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200306445111598175050435 300459667667397262575653)
                  ·
                    refine ⟨56336187687636986732935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 300459667667397262575653 56336187687636986732935)
                    ·
                      rfl

theorem cell23_329143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_329143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329143 prefixEnd_329143 := by exact prefixLift 329143
  have htrace : WordTrace (prefixWord ++ tailWord_329143) baseStart_329143 baseEnd_329143 := by
    simpa [prefixWord, tailWord_329143, baseEnd_329143] using wordTrace_append hprefix tailTrace_329143
  have hstable : (prefixWord ++ tailWord_329143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329143).length < 2 ^ (prefixWord ++ tailWord_329143).sum := by decide
  have hdescent : baseEnd_329143 < baseStart_329143 := by decide
  rcases family_descends (prefixWord ++ tailWord_329143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329159 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_329159 : Nat := 118140960795 + 329159 * 2 ^ 59
def prefixEnd_329159 : Nat := 4983230072969 + 3 ^ 40 * 329159 * 2
def baseEnd_329159 : Nat := 169016778753382897598731

theorem tailTrace_329159 : CollatzResearch.WordTrace tailWord_329159 prefixEnd_329159 169016778753382897598731 := by
  unfold tailWord_329159
  simp only [CollatzResearch.WordTrace]
  refine ⟨12005415014520633726734531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8003610009680422484489687 12005415014520633726734531)
  ·
    refine ⟨18008122521780950590101797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12005415014520633726734531 18008122521780950590101797)
    ·
      refine ⟨3376522972833928235644087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18008122521780950590101797 3376522972833928235644087)
      ·
        refine ⟨5064784459250892353466131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3376522972833928235644087 5064784459250892353466131)
        ·
          refine ⟨7597176688876338530199197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064784459250892353466131 7597176688876338530199197)
          ·
            refine ⟨2848941258328626948824699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7597176688876338530199197 2848941258328626948824699)
            ·
              refine ⟨4273411887492940423237049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848941258328626948824699 4273411887492940423237049)
              ·
                refine ⟨3205058915619705317427787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4273411887492940423237049 3205058915619705317427787)
                ·
                  refine ⟨4807588373429557976141681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205058915619705317427787 4807588373429557976141681)
                  ·
                    refine ⟨3605691280072168482106261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4807588373429557976141681 3605691280072168482106261)
                    ·
                      refine ⟨169016778753382897598731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3605691280072168482106261 169016778753382897598731)
                      ·
                        rfl

theorem cell23_329159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_329159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329159 prefixEnd_329159 := by exact prefixLift 329159
  have htrace : WordTrace (prefixWord ++ tailWord_329159) baseStart_329159 baseEnd_329159 := by
    simpa [prefixWord, tailWord_329159, baseEnd_329159] using wordTrace_append hprefix tailTrace_329159
  have hstable : (prefixWord ++ tailWord_329159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329159).length < 2 ^ (prefixWord ++ tailWord_329159).sum := by decide
  have hdescent : baseEnd_329159 < baseStart_329159 := by decide
  rcases family_descends (prefixWord ++ tailWord_329159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329200 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 3, 1, 3]
def baseStart_329200 : Nat := 118140960795 + 329200 * 2 ^ 59
def prefixEnd_329200 : Nat := 4983230072969 + 3 ^ 40 * 329200 * 2
def baseEnd_329200 : Nat := 169037831460217237186043

theorem tailTrace_329200 : CollatzResearch.WordTrace tailWord_329200 prefixEnd_329200 169037831460217237186043 := by
  unfold tailWord_329200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6003455203686048864488527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8004606938248065152651369 6003455203686048864488527)
  ·
    refine ⟨9005182805529073296732791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6003455203686048864488527 9005182805529073296732791)
    ·
      refine ⟨13507774208293609945099187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9005182805529073296732791 13507774208293609945099187)
      ·
        refine ⟨20261661312440414917648781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13507774208293609945099187 20261661312440414917648781)
        ·
          refine ⟨7598122992165155594118293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20261661312440414917648781 7598122992165155594118293)
          ·
            refine ⟨356162015257741668474295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7598122992165155594118293 356162015257741668474295)
            ·
              refine ⟨534243022886612502711443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356162015257741668474295 534243022886612502711443)
              ·
                refine ⟨801364534329918754067165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534243022886612502711443 801364534329918754067165)
                ·
                  refine ⟨300511700373719532775187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801364534329918754067165 300511700373719532775187)
                  ·
                    refine ⟨450767550560579299162781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300511700373719532775187 450767550560579299162781)
                    ·
                      refine ⟨169037831460217237186043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450767550560579299162781 169037831460217237186043)
                      ·
                        rfl

theorem cell23_329200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 1, 3].length) (baseStart_329200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329200 prefixEnd_329200 := by exact prefixLift 329200
  have htrace : WordTrace (prefixWord ++ tailWord_329200) baseStart_329200 baseEnd_329200 := by
    simpa [prefixWord, tailWord_329200, baseEnd_329200] using wordTrace_append hprefix tailTrace_329200
  have hstable : (prefixWord ++ tailWord_329200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329200).length < 2 ^ (prefixWord ++ tailWord_329200).sum := by decide
  have hdescent : baseEnd_329200 < baseStart_329200 := by decide
  rcases family_descends (prefixWord ++ tailWord_329200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329223 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_329223 : Nat := 118140960795 + 329223 * 2 ^ 59
def prefixEnd_329223 : Nat := 4983230072969 + 3 ^ 40 * 329223 * 2
def baseEnd_329223 : Nat := 169049641515270647198437

theorem tailTrace_329223 : CollatzResearch.WordTrace tailWord_329223 prefixEnd_329223 169049641515270647198437 := by
  unfold tailWord_329223
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007749286288772657064323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8005166190859181771376215 12007749286288772657064323)
  ·
    refine ⟨18011623929433158985596485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12007749286288772657064323 18011623929433158985596485)
    ·
      refine ⟨3377179486768717309799341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18011623929433158985596485 3377179486768717309799341)
      ·
        refine ⟨1266442307538268991174753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3377179486768717309799341 1266442307538268991174753)
        ·
          refine ⟨949831730653701743381065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266442307538268991174753 949831730653701743381065)
          ·
            refine ⟨712373797990276307535799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 949831730653701743381065 712373797990276307535799)
            ·
              refine ⟨1068560696985414461303699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712373797990276307535799 1068560696985414461303699)
              ·
                refine ⟨1602841045478121691955549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068560696985414461303699 1602841045478121691955549)
                ·
                  refine ⟨601065392054295634483331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1602841045478121691955549 601065392054295634483331)
                  ·
                    refine ⟨901598088081443451724997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 601065392054295634483331 901598088081443451724997)
                    ·
                      refine ⟨169049641515270647198437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 901598088081443451724997 169049641515270647198437)
                      ·
                        rfl

theorem cell23_329223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_329223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329223 prefixEnd_329223 := by exact prefixLift 329223
  have htrace : WordTrace (prefixWord ++ tailWord_329223) baseStart_329223 baseEnd_329223 := by
    simpa [prefixWord, tailWord_329223, baseEnd_329223] using wordTrace_append hprefix tailTrace_329223
  have hstable : (prefixWord ++ tailWord_329223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329223).length < 2 ^ (prefixWord ++ tailWord_329223).sum := by decide
  have hdescent : baseEnd_329223 < baseStart_329223 := by decide
  rcases family_descends (prefixWord ++ tailWord_329223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329251 : List Nat := [1, 1, 1, 4, 6, 1, 2, 2, 1, 1, 3]
def baseStart_329251 : Nat := 118140960795 + 329251 * 2 ^ 59
def prefixEnd_329251 : Nat := 4983230072969 + 3 ^ 40 * 329251 * 2
def baseEnd_329251 : Nat := 169064018973596537648309

theorem tailTrace_329251 : CollatzResearch.WordTrace tailWord_329251 prefixEnd_329251 169064018973596537648309 := by
  unfold tailWord_329251
  simp only [CollatzResearch.WordTrace]
  refine ⟨12008770530187333439083607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8005847020124888959389071 12008770530187333439083607)
  ·
    refine ⟨18013155795281000158625411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12008770530187333439083607 18013155795281000158625411)
    ·
      refine ⟨27019733692921500237938117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18013155795281000158625411 27019733692921500237938117)
      ·
        refine ⟨5066200067422781294613397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27019733692921500237938117 5066200067422781294613397)
        ·
          refine ⟨237478128160442873185003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5066200067422781294613397 237478128160442873185003)
          ·
            refine ⟨356217192240664309777505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237478128160442873185003 356217192240664309777505)
            ·
              refine ⟨267162894180498232333129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356217192240664309777505 267162894180498232333129)
              ·
                refine ⟨200372170635373674249847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267162894180498232333129 200372170635373674249847)
                ·
                  refine ⟨300558255953060511374771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200372170635373674249847 300558255953060511374771)
                  ·
                    refine ⟨450837383929590767062157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300558255953060511374771 450837383929590767062157)
                    ·
                      refine ⟨169064018973596537648309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450837383929590767062157 169064018973596537648309)
                      ·
                        rfl

theorem cell23_329251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_329251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329251 prefixEnd_329251 := by exact prefixLift 329251
  have htrace : WordTrace (prefixWord ++ tailWord_329251) baseStart_329251 baseEnd_329251 := by
    simpa [prefixWord, tailWord_329251, baseEnd_329251] using wordTrace_append hprefix tailTrace_329251
  have hstable : (prefixWord ++ tailWord_329251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329251).length < 2 ^ (prefixWord ++ tailWord_329251).sum := by decide
  have hdescent : baseEnd_329251 < baseStart_329251 := by decide
  rcases family_descends (prefixWord ++ tailWord_329251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329273 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 3]
def baseStart_329273 : Nat := 118140960795 + 329273 * 2 ^ 59
def prefixEnd_329273 : Nat := 4983230072969 + 3 ^ 40 * 329273 * 2
def baseEnd_329273 : Nat := 169075315547995451573207

theorem tailTrace_329273 : CollatzResearch.WordTrace tailWord_329273 prefixEnd_329273 169075315547995451573207 := by
  unfold tailWord_329273
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009572936107631196384473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8006381957405087464256315 12009572936107631196384473)
  ·
    refine ⟨9007179702080723397288355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12009572936107631196384473 9007179702080723397288355)
    ·
      refine ⟨13510769553121085095932533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9007179702080723397288355 13510769553121085095932533)
      ·
        refine ⟨1266634645605101727743675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13510769553121085095932533 1266634645605101727743675)
        ·
          refine ⟨1899951968407652591615513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266634645605101727743675 1899951968407652591615513)
          ·
            refine ⟨1424963976305739443711635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899951968407652591615513 1424963976305739443711635)
            ·
              refine ⟨2137445964458609165567453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424963976305739443711635 2137445964458609165567453)
              ·
                refine ⟨801542236671978437087795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137445964458609165567453 801542236671978437087795)
                ·
                  refine ⟨1202313355007967655631693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801542236671978437087795 1202313355007967655631693)
                  ·
                    refine ⟨450867508127987870861885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202313355007967655631693 450867508127987870861885)
                    ·
                      refine ⟨169075315547995451573207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 450867508127987870861885 169075315547995451573207)
                      ·
                        rfl

theorem cell23_329273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_329273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329273 prefixEnd_329273 := by exact prefixLift 329273
  have htrace : WordTrace (prefixWord ++ tailWord_329273) baseStart_329273 baseEnd_329273 := by
    simpa [prefixWord, tailWord_329273, baseEnd_329273] using wordTrace_append hprefix tailTrace_329273
  have hstable : (prefixWord ++ tailWord_329273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329273).length < 2 ^ (prefixWord ++ tailWord_329273).sum := by decide
  have hdescent : baseEnd_329273 < baseStart_329273 := by decide
  rcases family_descends (prefixWord ++ tailWord_329273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329334 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_329334 : Nat := 118140960795 + 329334 * 2 ^ 59
def prefixEnd_329334 : Nat := 4983230072969 + 3 ^ 40 * 329334 * 2
def baseEnd_329334 : Nat := 169106637867919712910427

theorem tailTrace_329334 : CollatzResearch.WordTrace tailWord_329334 prefixEnd_329334 169106637867919712910427 := by
  unfold tailWord_329334
  simp only [CollatzResearch.WordTrace]
  refine ⟨750737361805414913397191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8007865192591092409570037 750737361805414913397191)
  ·
    refine ⟨1126106042708122370095787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 750737361805414913397191 1126106042708122370095787)
    ·
      refine ⟨1689159064062183555143681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126106042708122370095787 1689159064062183555143681)
      ·
        refine ⟨1266869298046637666357761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689159064062183555143681 1266869298046637666357761)
        ·
          refine ⟨950151973534978249768321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266869298046637666357761 950151973534978249768321)
          ·
            refine ⟨712613980151233687326241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950151973534978249768321 712613980151233687326241)
            ·
              refine ⟨534460485113425265494681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712613980151233687326241 534460485113425265494681)
              ·
                refine ⟨400845363835068949121011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534460485113425265494681 400845363835068949121011)
                ·
                  refine ⟨601268045752603423681517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400845363835068949121011 601268045752603423681517)
                  ·
                    refine ⟨225475517157226283880569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 601268045752603423681517 225475517157226283880569)
                    ·
                      refine ⟨169106637867919712910427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225475517157226283880569 169106637867919712910427)
                      ·
                        rfl

theorem cell23_329334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_329334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329334 prefixEnd_329334 := by exact prefixLift 329334
  have htrace : WordTrace (prefixWord ++ tailWord_329334) baseStart_329334 baseEnd_329334 := by
    simpa [prefixWord, tailWord_329334, baseEnd_329334] using wordTrace_append hprefix tailTrace_329334
  have hstable : (prefixWord ++ tailWord_329334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329334).length < 2 ^ (prefixWord ++ tailWord_329334).sum := by decide
  have hdescent : baseEnd_329334 < baseStart_329334 := by decide
  rcases family_descends (prefixWord ++ tailWord_329334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329413 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_329413 : Nat := 118140960795 + 329413 * 2 ^ 59
def prefixEnd_329413 : Nat := 4983230072969 + 3 ^ 40 * 329413 * 2
def baseEnd_329413 : Nat := 56382400946541634607521

theorem tailTrace_329413 : CollatzResearch.WordTrace tailWord_329413 prefixEnd_329413 56382400946541634607521 := by
  unfold tailWord_329413
  simp only [CollatzResearch.WordTrace]
  refine ⟨12014679155600435106480893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8009786103733623404320595 12014679155600435106480893)
  ·
    refine ⟨4505504683350163164930335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12014679155600435106480893 4505504683350163164930335)
    ·
      refine ⟨6758257025025244747395503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4505504683350163164930335 6758257025025244747395503)
      ·
        refine ⟨10137385537537867121093255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758257025025244747395503 10137385537537867121093255)
        ·
          refine ⟨15206078306306800681639883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10137385537537867121093255 15206078306306800681639883)
          ·
            refine ⟨22809117459460201022459825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15206078306306800681639883 22809117459460201022459825)
            ·
              refine ⟨17106838094595150766844869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22809117459460201022459825 17106838094595150766844869)
              ·
                refine ⟨3207532142736590768783413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17106838094595150766844869 3207532142736590768783413)
                ·
                  refine ⟨300706138381555384573445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207532142736590768783413 300706138381555384573445)
                  ·
                    refine ⟨56382400946541634607521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 300706138381555384573445 56382400946541634607521)
                    ·
                      rfl

theorem cell23_329413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_329413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329413 prefixEnd_329413 := by exact prefixLift 329413
  have htrace : WordTrace (prefixWord ++ tailWord_329413) baseStart_329413 baseEnd_329413 := by
    simpa [prefixWord, tailWord_329413, baseEnd_329413] using wordTrace_append hprefix tailTrace_329413
  have hstable : (prefixWord ++ tailWord_329413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329413).length < 2 ^ (prefixWord ++ tailWord_329413).sum := by decide
  have hdescent : baseEnd_329413 < baseStart_329413 := by decide
  rcases family_descends (prefixWord ++ tailWord_329413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329421 : List Nat := [1, 6, 2, 1, 1, 3, 2, 2, 5]
def baseStart_329421 : Nat := 118140960795 + 329421 * 2 ^ 59
def prefixEnd_329421 : Nat := 4983230072969 + 3 ^ 40 * 329421 * 2
def baseEnd_329421 : Nat := 18794590076095652502503

theorem tailTrace_329421 : CollatzResearch.WordTrace tailWord_329421 prefixEnd_329421 18794590076095652502503 := by
  unfold tailWord_329421
  simp only [CollatzResearch.WordTrace]
  refine ⟨12014970939571452472772117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8009980626380968315181411 12014970939571452472772117)
  ·
    refine ⟨563201762792411834661193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12014970939571452472772117 563201762792411834661193)
    ·
      refine ⟨422401322094308875995895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 563201762792411834661193 422401322094308875995895)
      ·
        refine ⟨633601983141463313993843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422401322094308875995895 633601983141463313993843)
        ·
          refine ⟨950402974712194970990765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633601983141463313993843 950402974712194970990765)
          ·
            refine ⟨356401115517073114121537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 950402974712194970990765 356401115517073114121537)
            ·
              refine ⟨267300836637804835591153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356401115517073114121537 267300836637804835591153)
              ·
                refine ⟨200475627478353626693365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267300836637804835591153 200475627478353626693365)
                ·
                  refine ⟨18794590076095652502503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200475627478353626693365 18794590076095652502503)
                  ·
                    rfl

theorem cell23_329421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_329421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329421 prefixEnd_329421 := by exact prefixLift 329421
  have htrace : WordTrace (prefixWord ++ tailWord_329421) baseStart_329421 baseEnd_329421 := by
    simpa [prefixWord, tailWord_329421, baseEnd_329421] using wordTrace_append hprefix tailTrace_329421
  have hstable : (prefixWord ++ tailWord_329421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329421).length < 2 ^ (prefixWord ++ tailWord_329421).sum := by decide
  have hdescent : baseEnd_329421 < baseStart_329421 := by decide
  rcases family_descends (prefixWord ++ tailWord_329421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329457 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_329457 : Nat := 118140960795 + 329457 * 2 ^ 59
def prefixEnd_329457 : Nat := 4983230072969 + 3 ^ 40 * 329457 * 2
def baseEnd_329457 : Nat := 169169795988422731672361

theorem tailTrace_329457 : CollatzResearch.WordTrace tailWord_329457 prefixEnd_329457 169169795988422731672361 := by
  unfold tailWord_329457
  simp only [CollatzResearch.WordTrace]
  refine ⟨12016283967441030621082625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8010855978294020414055083 12016283967441030621082625)
  ·
    refine ⟨9012212975580772965811969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12016283967441030621082625 9012212975580772965811969)
    ·
      refine ⟨6759159731685579724358977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9012212975580772965811969 6759159731685579724358977)
      ·
        refine ⟨5069369798764184793269233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6759159731685579724358977 5069369798764184793269233)
        ·
          refine ⟨3802027349073138594951925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5069369798764184793269233 3802027349073138594951925)
          ·
            refine ⟨356440063975606743276743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3802027349073138594951925 356440063975606743276743)
            ·
              refine ⟨534660095963410114915115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356440063975606743276743 534660095963410114915115)
              ·
                refine ⟨801990143945115172372673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534660095963410114915115 801990143945115172372673)
                ·
                  refine ⟨601492607958836379279505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 801990143945115172372673 601492607958836379279505)
                  ·
                    refine ⟨451119455969127284459629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 601492607958836379279505 451119455969127284459629)
                    ·
                      refine ⟨169169795988422731672361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 451119455969127284459629 169169795988422731672361)
                      ·
                        rfl

theorem cell23_329457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_329457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329457 prefixEnd_329457 := by exact prefixLift 329457
  have htrace : WordTrace (prefixWord ++ tailWord_329457) baseStart_329457 baseEnd_329457 := by
    simpa [prefixWord, tailWord_329457, baseEnd_329457] using wordTrace_append hprefix tailTrace_329457
  have hstable : (prefixWord ++ tailWord_329457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329457).length < 2 ^ (prefixWord ++ tailWord_329457).sum := by decide
  have hdescent : baseEnd_329457 < baseStart_329457 := by decide
  rcases family_descends (prefixWord ++ tailWord_329457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329521 : List Nat := [1, 2, 2, 3, 2, 4, 1, 3, 1, 1, 3]
def baseStart_329521 : Nat := 118140960795 + 329521 * 2 ^ 59
def prefixEnd_329521 : Nat := 4983230072969 + 3 ^ 40 * 329521 * 2
def baseEnd_329521 : Nat := 169202658750310481272067

theorem tailTrace_329521 : CollatzResearch.WordTrace tailWord_329521 prefixEnd_329521 169202658750310481272067 := by
  unfold tailWord_329521
  simp only [CollatzResearch.WordTrace]
  refine ⟨12018618239209169551412417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8012412159472779700941611 12018618239209169551412417)
  ·
    refine ⟨9013963679406877163559313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12018618239209169551412417 9013963679406877163559313)
    ·
      refine ⟨6760472759555157872669485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9013963679406877163559313 6760472759555157872669485)
      ·
        refine ⟨2535177284833184202251057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6760472759555157872669485 2535177284833184202251057)
        ·
          refine ⟨1901382963624888151688293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2535177284833184202251057 1901382963624888151688293)
          ·
            refine ⟨356509305679666528441555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1901382963624888151688293 356509305679666528441555)
            ·
              refine ⟨534763958519499792662333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356509305679666528441555 534763958519499792662333)
              ·
                refine ⟨200536484444812422248375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 534763958519499792662333 200536484444812422248375)
                ·
                  refine ⟨300804726667218633372563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200536484444812422248375 300804726667218633372563)
                  ·
                    refine ⟨451207090000827950058845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300804726667218633372563 451207090000827950058845)
                    ·
                      refine ⟨169202658750310481272067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 451207090000827950058845 169202658750310481272067)
                      ·
                        rfl

theorem cell23_329521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_329521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329521 prefixEnd_329521 := by exact prefixLift 329521
  have htrace : WordTrace (prefixWord ++ tailWord_329521) baseStart_329521 baseEnd_329521 := by
    simpa [prefixWord, tailWord_329521, baseEnd_329521] using wordTrace_append hprefix tailTrace_329521
  have hstable : (prefixWord ++ tailWord_329521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329521).length < 2 ^ (prefixWord ++ tailWord_329521).sum := by decide
  have hdescent : baseEnd_329521 < baseStart_329521 := by decide
  rcases family_descends (prefixWord ++ tailWord_329521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329530 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_329530 : Nat := 118140960795 + 329530 * 2 ^ 59
def prefixEnd_329530 : Nat := 4983230072969 + 3 ^ 40 * 329530 * 2
def baseEnd_329530 : Nat := 169207280076200946059525

theorem tailTrace_329530 : CollatzResearch.WordTrace tailWord_329530 prefixEnd_329530 169207280076200946059525 := by
  unfold tailWord_329530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004736624044141022122511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8012630997451042725660029 3004736624044141022122511)
  ·
    refine ⟨4507104936066211533183767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3004736624044141022122511 4507104936066211533183767)
    ·
      refine ⟨6760657404099317299775651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4507104936066211533183767 6760657404099317299775651)
      ·
        refine ⟨10140986106148975949663477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6760657404099317299775651 10140986106148975949663477)
        ·
          refine ⟨950717447451466495280951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10140986106148975949663477 950717447451466495280951)
          ·
            refine ⟨1426076171177199742921427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950717447451466495280951 1426076171177199742921427)
            ·
              refine ⟨2139114256765799614382141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426076171177199742921427 2139114256765799614382141)
              ·
                refine ⟨802167846287174855393303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2139114256765799614382141 802167846287174855393303)
                ·
                  refine ⟨1203251769430762283089955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802167846287174855393303 1203251769430762283089955)
                  ·
                    refine ⟨1804877654146143424634933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1203251769430762283089955 1804877654146143424634933)
                    ·
                      refine ⟨169207280076200946059525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1804877654146143424634933 169207280076200946059525)
                      ·
                        rfl

theorem cell23_329530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_329530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329530 prefixEnd_329530 := by exact prefixLift 329530
  have htrace : WordTrace (prefixWord ++ tailWord_329530) baseStart_329530 baseEnd_329530 := by
    simpa [prefixWord, tailWord_329530, baseEnd_329530] using wordTrace_append hprefix tailTrace_329530
  have hstable : (prefixWord ++ tailWord_329530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329530).length < 2 ^ (prefixWord ++ tailWord_329530).sum := by decide
  have hdescent : baseEnd_329530 < baseStart_329530 := by decide
  rcases family_descends (prefixWord ++ tailWord_329530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329544 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_329544 : Nat := 118140960795 + 329544 * 2 ^ 59
def prefixEnd_329544 : Nat := 4983230072969 + 3 ^ 40 * 329544 * 2
def baseEnd_329544 : Nat := 169214468805363891284461

theorem tailTrace_329544 : CollatzResearch.WordTrace tailWord_329544 prefixEnd_329544 169214468805363891284461 := by
  unfold tailWord_329544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6009728559062922239749843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8012971412083896319666457 6009728559062922239749843)
  ·
    refine ⟨9014592838594383359624765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6009728559062922239749843 9014592838594383359624765)
    ·
      refine ⟨3380472314472893759859287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9014592838594383359624765 3380472314472893759859287)
      ·
        refine ⟨5070708471709340639788931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380472314472893759859287 5070708471709340639788931)
        ·
          refine ⟨7606062707564010959683397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070708471709340639788931 7606062707564010959683397)
          ·
            refine ⟨1426136757668252054940637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7606062707564010959683397 1426136757668252054940637)
            ·
              refine ⟨534801284125594520602739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1426136757668252054940637 534801284125594520602739)
              ·
                refine ⟨802201926188391780904109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534801284125594520602739 802201926188391780904109)
                ·
                  refine ⟨300825722320646917839041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802201926188391780904109 300825722320646917839041)
                  ·
                    refine ⟨225619291740485188379281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 300825722320646917839041 225619291740485188379281)
                    ·
                      refine ⟨169214468805363891284461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225619291740485188379281 169214468805363891284461)
                      ·
                        rfl

theorem cell23_329544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_329544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329544 prefixEnd_329544 := by exact prefixLift 329544
  have htrace : WordTrace (prefixWord ++ tailWord_329544) baseStart_329544 baseEnd_329544 := by
    simpa [prefixWord, tailWord_329544, baseEnd_329544] using wordTrace_append hprefix tailTrace_329544
  have hstable : (prefixWord ++ tailWord_329544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329544).length < 2 ^ (prefixWord ++ tailWord_329544).sum := by decide
  have hdescent : baseEnd_329544 < baseStart_329544 := by decide
  rcases family_descends (prefixWord ++ tailWord_329544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329554 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_329554 : Nat := 118140960795 + 329554 * 2 ^ 59
def prefixEnd_329554 : Nat := 4983230072969 + 3 ^ 40 * 329554 * 2
def baseEnd_329554 : Nat := 56406534537302950719805

theorem tailTrace_329554 : CollatzResearch.WordTrace tailWord_329554 prefixEnd_329554 56406534537302950719805 := by
  unfold tailWord_329554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004955462022404046840929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8013214565393077458242477 3004955462022404046840929)
  ·
    refine ⟨2253716596516803035130697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3004955462022404046840929 2253716596516803035130697)
    ·
      refine ⟨1690287447387602276348023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2253716596516803035130697 1690287447387602276348023)
      ·
        refine ⟨2535431171081403414522035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1690287447387602276348023 2535431171081403414522035)
        ·
          refine ⟨3803146756622105121783053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535431171081403414522035 3803146756622105121783053)
          ·
            refine ⟨1426180033733289420668645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3803146756622105121783053 1426180033733289420668645)
            ·
              refine ⟨267408756324991766375371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1426180033733289420668645 267408756324991766375371)
              ·
                refine ⟨401113134487487649563057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267408756324991766375371 401113134487487649563057)
                ·
                  refine ⟨300834850865615737172293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401113134487487649563057 300834850865615737172293)
                  ·
                    refine ⟨56406534537302950719805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 300834850865615737172293 56406534537302950719805)
                    ·
                      rfl

theorem cell23_329554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_329554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329554 prefixEnd_329554 := by exact prefixLift 329554
  have htrace : WordTrace (prefixWord ++ tailWord_329554) baseStart_329554 baseEnd_329554 := by
    simpa [prefixWord, tailWord_329554, baseEnd_329554] using wordTrace_append hprefix tailTrace_329554
  have hstable : (prefixWord ++ tailWord_329554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329554).length < 2 ^ (prefixWord ++ tailWord_329554).sum := by decide
  have hdescent : baseEnd_329554 < baseStart_329554 := by decide
  rcases family_descends (prefixWord ++ tailWord_329554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329564 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_329564 : Nat := 118140960795 + 329564 * 2 ^ 59
def prefixEnd_329564 : Nat := 4983230072969 + 3 ^ 40 * 329564 * 2
def baseEnd_329564 : Nat := 169224738418453813034369

theorem tailTrace_329564 : CollatzResearch.WordTrace tailWord_329564 prefixEnd_329564 169224738418453813034369 := by
  unfold tailWord_329564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010093289026693947613873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8013457718702258596818497 6010093289026693947613873)
  ·
    refine ⟨4507569966770020460710405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6010093289026693947613873 4507569966770020460710405)
    ·
      refine ⟨845169368769378836383201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4507569966770020460710405 845169368769378836383201)
      ·
        refine ⟨633877026577034127287401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 845169368769378836383201 633877026577034127287401)
        ·
          refine ⟨475407769932775595465551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633877026577034127287401 475407769932775595465551)
          ·
            refine ⟨713111654899163393198327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475407769932775595465551 713111654899163393198327)
            ·
              refine ⟨1069667482348745089797491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713111654899163393198327 1069667482348745089797491)
              ·
                refine ⟨1604501223523117634696237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069667482348745089797491 1604501223523117634696237)
                ·
                  refine ⟨601687958821169113011089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1604501223523117634696237 601687958821169113011089)
                  ·
                    refine ⟨451265969115876834758317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 601687958821169113011089 451265969115876834758317)
                    ·
                      refine ⟨169224738418453813034369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 451265969115876834758317 169224738418453813034369)
                      ·
                        rfl

theorem cell23_329564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_329564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329564 prefixEnd_329564 := by exact prefixLift 329564
  have htrace : WordTrace (prefixWord ++ tailWord_329564) baseStart_329564 baseEnd_329564 := by
    simpa [prefixWord, tailWord_329564, baseEnd_329564] using wordTrace_append hprefix tailTrace_329564
  have hstable : (prefixWord ++ tailWord_329564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329564).length < 2 ^ (prefixWord ++ tailWord_329564).sum := by decide
  have hdescent : baseEnd_329564 < baseStart_329564 := by decide
  rcases family_descends (prefixWord ++ tailWord_329564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329617 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 1, 4, 2]
def baseStart_329617 : Nat := 118140960795 + 329617 * 2 ^ 59
def prefixEnd_329617 : Nat := 4983230072969 + 3 ^ 40 * 329617 * 2
def baseEnd_329617 : Nat := 169251952893142105671625

theorem tailTrace_329617 : CollatzResearch.WordTrace tailWord_329617 prefixEnd_329617 169251952893142105671625 := by
  unfold tailWord_329617
  simp only [CollatzResearch.WordTrace]
  refine ⟨12022119646861377946907105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8014746431240918631271403 12022119646861377946907105)
  ·
    refine ⟨9016589735146033460180329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12022119646861377946907105 9016589735146033460180329)
    ·
      refine ⟨6762442301359525095135247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9016589735146033460180329 6762442301359525095135247)
      ·
        refine ⟨10143663452039287642702871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6762442301359525095135247 10143663452039287642702871)
        ·
          refine ⟨15215495178058931464054307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10143663452039287642702871 15215495178058931464054307)
          ·
            refine ⟨22823242767088397196081461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15215495178058931464054307 22823242767088397196081461)
            ·
              refine ⟨2139679009414537237132637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22823242767088397196081461 2139679009414537237132637)
              ·
                refine ⟨802379628530451463924739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2139679009414537237132637 802379628530451463924739)
                ·
                  refine ⟨1203569442795677195887109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802379628530451463924739 1203569442795677195887109)
                  ·
                    refine ⟨225669270524189474228833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203569442795677195887109 225669270524189474228833)
                    ·
                      refine ⟨169251952893142105671625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225669270524189474228833 169251952893142105671625)
                      ·
                        rfl

theorem cell23_329617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_329617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329617 prefixEnd_329617 := by exact prefixLift 329617
  have htrace : WordTrace (prefixWord ++ tailWord_329617) baseStart_329617 baseEnd_329617 := by
    simpa [prefixWord, tailWord_329617, baseEnd_329617] using wordTrace_append hprefix tailTrace_329617
  have hstable : (prefixWord ++ tailWord_329617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329617).length < 2 ^ (prefixWord ++ tailWord_329617).sum := by decide
  have hdescent : baseEnd_329617 < baseStart_329617 := by decide
  rcases family_descends (prefixWord ++ tailWord_329617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329657 : List Nat := [1, 2, 1, 4, 2, 1, 1, 6, 5]
def baseStart_329657 : Nat := 118140960795 + 329657 * 2 ^ 59
def prefixEnd_329657 : Nat := 4983230072969 + 3 ^ 40 * 329657 * 2
def baseEnd_329657 : Nat := 18808054679924661019049

theorem tailTrace_329657 : CollatzResearch.WordTrace tailWord_329657 prefixEnd_329657 18808054679924661019049 := by
  unfold tailWord_329657
  simp only [CollatzResearch.WordTrace]
  refine ⟨12023578566716464778363225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8015719044477643185575483 12023578566716464778363225)
  ·
    refine ⟨9017683925037348583772419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12023578566716464778363225 9017683925037348583772419)
    ·
      refine ⟨13526525887556022875658629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9017683925037348583772419 13526525887556022875658629)
      ·
        refine ⟨2536223603916754289185993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13526525887556022875658629 2536223603916754289185993)
        ·
          refine ⟨1902167702937565716889495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2536223603916754289185993 1902167702937565716889495)
          ·
            refine ⟨2853251554406348575334243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902167702937565716889495 2853251554406348575334243)
            ·
              refine ⟨4279877331609522863001365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853251554406348575334243 4279877331609522863001365)
              ·
                refine ⟨200619249919196384203189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4279877331609522863001365 200619249919196384203189)
                ·
                  refine ⟨18808054679924661019049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200619249919196384203189 18808054679924661019049)
                  ·
                    rfl

theorem cell23_329657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 5].length) (baseStart_329657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329657 prefixEnd_329657 := by exact prefixLift 329657
  have htrace : WordTrace (prefixWord ++ tailWord_329657) baseStart_329657 baseEnd_329657 := by
    simpa [prefixWord, tailWord_329657, baseEnd_329657] using wordTrace_append hprefix tailTrace_329657
  have hstable : (prefixWord ++ tailWord_329657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329657).length < 2 ^ (prefixWord ++ tailWord_329657).sum := by decide
  have hdescent : baseEnd_329657 < baseStart_329657 := by decide
  rcases family_descends (prefixWord ++ tailWord_329657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329707 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 4, 4, 2]
def baseStart_329707 : Nat := 118140960795 + 329707 * 2 ^ 59
def prefixEnd_329707 : Nat := 4983230072969 + 3 ^ 40 * 329707 * 2
def baseEnd_329707 : Nat := 169298166152046753546211

theorem tailTrace_329707 : CollatzResearch.WordTrace tailWord_329707 prefixEnd_329707 169298166152046753546211 := by
  unfold tailWord_329707
  simp only [CollatzResearch.WordTrace]
  refine ⟨12025402216535323317683375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8016934811023548878455583 12025402216535323317683375)
  ·
    refine ⟨18038103324802984976525063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12025402216535323317683375 18038103324802984976525063)
    ·
      refine ⟨27057154987204477464787595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18038103324802984976525063 27057154987204477464787595)
      ·
        refine ⟨40585732480806716197181393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27057154987204477464787595 40585732480806716197181393)
        ·
          refine ⟨30439299360605037147886045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40585732480806716197181393 30439299360605037147886045)
          ·
            refine ⟨11414737260226888930457267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30439299360605037147886045 11414737260226888930457267)
            ·
              refine ⟨17122105890340333395685901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11414737260226888930457267 17122105890340333395685901)
              ·
                refine ⟨6420789708877625023382213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17122105890340333395685901 6420789708877625023382213)
                ·
                  refine ⟨1203898070414554691884165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6420789708877625023382213 1203898070414554691884165)
                  ·
                    refine ⟨225730888202729004728281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203898070414554691884165 225730888202729004728281)
                    ·
                      refine ⟨169298166152046753546211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225730888202729004728281 169298166152046753546211)
                      ·
                        rfl

theorem cell23_329707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4, 2].length) (baseStart_329707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329707 prefixEnd_329707 := by exact prefixLift 329707
  have htrace : WordTrace (prefixWord ++ tailWord_329707) baseStart_329707 baseEnd_329707 := by
    simpa [prefixWord, tailWord_329707, baseEnd_329707] using wordTrace_append hprefix tailTrace_329707
  have hstable : (prefixWord ++ tailWord_329707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329707).length < 2 ^ (prefixWord ++ tailWord_329707).sum := by decide
  have hdescent : baseEnd_329707 < baseStart_329707 := by decide
  rcases family_descends (prefixWord ++ tailWord_329707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329720 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_329720 : Nat := 118140960795 + 329720 * 2 ^ 59
def prefixEnd_329720 : Nat := 4983230072969 + 3 ^ 40 * 329720 * 2
def baseEnd_329720 : Nat := 169304841400555202683651

theorem tailTrace_329720 : CollatzResearch.WordTrace tailWord_329720 prefixEnd_329720 169304841400555202683651 := by
  unfold tailWord_329720
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012938182744113268953307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8017250910325484358604409 6012938182744113268953307)
  ·
    refine ⟨9019407274116169903429961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6012938182744113268953307 9019407274116169903429961)
    ·
      refine ⟨6764555455587127427572471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9019407274116169903429961 6764555455587127427572471)
      ·
        refine ⟨10146833183380691141358707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6764555455587127427572471 10146833183380691141358707)
        ·
          refine ⟨15220249775071036712038061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10146833183380691141358707 15220249775071036712038061)
          ·
            refine ⟨5707593665651638767014273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15220249775071036712038061 5707593665651638767014273)
            ·
              refine ⟨4280695249238729075260705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5707593665651638767014273 4280695249238729075260705)
              ·
                refine ⟨3210521436929046806445529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280695249238729075260705 3210521436929046806445529)
                ·
                  refine ⟨2407891077696785104834147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3210521436929046806445529 2407891077696785104834147)
                  ·
                    refine ⟨3611836616545177657251221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2407891077696785104834147 3611836616545177657251221)
                    ·
                      refine ⟨169304841400555202683651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3611836616545177657251221 169304841400555202683651)
                      ·
                        rfl

theorem cell23_329720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_329720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329720 prefixEnd_329720 := by exact prefixLift 329720
  have htrace : WordTrace (prefixWord ++ tailWord_329720) baseStart_329720 baseEnd_329720 := by
    simpa [prefixWord, tailWord_329720, baseEnd_329720] using wordTrace_append hprefix tailTrace_329720
  have hstable : (prefixWord ++ tailWord_329720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329720).length < 2 ^ (prefixWord ++ tailWord_329720).sum := by decide
  have hdescent : baseEnd_329720 < baseStart_329720 := by decide
  rcases family_descends (prefixWord ++ tailWord_329720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329777 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 3, 5]
def baseStart_329777 : Nat := 118140960795 + 329777 * 2 ^ 59
def prefixEnd_329777 : Nat := 4983230072969 + 3 ^ 40 * 329777 * 2
def baseEnd_329777 : Nat := 56444703265953826556963

theorem tailTrace_329777 : CollatzResearch.WordTrace tailWord_329777 prefixEnd_329777 56444703265953826556963 := by
  unfold tailWord_329777
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027955326281725272731585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8018636884187816848487723 12027955326281725272731585)
  ·
    refine ⟨9020966494711293954548689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12027955326281725272731585 9020966494711293954548689)
    ·
      refine ⟨6765724871033470465911517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9020966494711293954548689 6765724871033470465911517)
      ·
        refine ⟨2537146826637551424716819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6765724871033470465911517 2537146826637551424716819)
        ·
          refine ⟨3805720239956327137075229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537146826637551424716819 3805720239956327137075229)
          ·
            refine ⟨1427145089983622676403211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3805720239956327137075229 1427145089983622676403211)
            ·
              refine ⟨2140717634975434014604817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427145089983622676403211 2140717634975434014604817)
              ·
                refine ⟨1605538226231575510953613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140717634975434014604817 1605538226231575510953613)
                ·
                  refine ⟨602076834836840816607605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1605538226231575510953613 602076834836840816607605)
                  ·
                    refine ⟨56444703265953826556963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 602076834836840816607605 56444703265953826556963)
                    ·
                      rfl

theorem cell23_329777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_329777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329777 prefixEnd_329777 := by exact prefixLift 329777
  have htrace : WordTrace (prefixWord ++ tailWord_329777) baseStart_329777 baseEnd_329777 := by
    simpa [prefixWord, tailWord_329777, baseEnd_329777] using wordTrace_append hprefix tailTrace_329777
  have hstable : (prefixWord ++ tailWord_329777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329777).length < 2 ^ (prefixWord ++ tailWord_329777).sum := by decide
  have hdescent : baseEnd_329777 < baseStart_329777 := by decide
  rcases family_descends (prefixWord ++ tailWord_329777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329807 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 6, 4]
def baseStart_329807 : Nat := 118140960795 + 329807 * 2 ^ 59
def prefixEnd_329807 : Nat := 4983230072969 + 3 ^ 40 * 329807 * 2
def baseEnd_329807 : Nat := 56449838072498787431917

theorem tailTrace_329807 : CollatzResearch.WordTrace tailWord_329807 prefixEnd_329807 56449838072498787431917 := by
  unfold tailWord_329807
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029049516173040396323675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8019366344115360264215783 12029049516173040396323675)
  ·
    refine ⟨18043574274259560594485513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12029049516173040396323675 18043574274259560594485513)
    ·
      refine ⟨13532680705694670445864135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18043574274259560594485513 13532680705694670445864135)
      ·
        refine ⟨20299021058542005668796203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13532680705694670445864135 20299021058542005668796203)
        ·
          refine ⟨30448531587813008503194305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20299021058542005668796203 30448531587813008503194305)
          ·
            refine ⟨22836398690859756377395729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30448531587813008503194305 22836398690859756377395729)
            ·
              refine ⟨17127299018144817283046797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22836398690859756377395729 17127299018144817283046797)
              ·
                refine ⟨6422737131804306481142549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17127299018144817283046797 6422737131804306481142549)
                ·
                  refine ⟨301065803053326866303557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6422737131804306481142549 301065803053326866303557)
                  ·
                    refine ⟨56449838072498787431917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301065803053326866303557 56449838072498787431917)
                    ·
                      rfl

theorem cell23_329807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_329807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329807 prefixEnd_329807 := by exact prefixLift 329807
  have htrace : WordTrace (prefixWord ++ tailWord_329807) baseStart_329807 baseEnd_329807 := by
    simpa [prefixWord, tailWord_329807, baseEnd_329807] using wordTrace_append hprefix tailTrace_329807
  have hstable : (prefixWord ++ tailWord_329807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329807).length < 2 ^ (prefixWord ++ tailWord_329807).sum := by decide
  have hdescent : baseEnd_329807 < baseStart_329807 := by decide
  rcases family_descends (prefixWord ++ tailWord_329807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329817 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_329817 : Nat := 118140960795 + 329817 * 2 ^ 59
def prefixEnd_329817 : Nat := 4983230072969 + 3 ^ 40 * 329817 * 2
def baseEnd_329817 : Nat := 169354649024041323170705

theorem tailTrace_329817 : CollatzResearch.WordTrace tailWord_329817 prefixEnd_329817 169354649024041323170705 := by
  unfold tailWord_329817
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029414246136812104187705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8019609497424541402791803 12029414246136812104187705)
  ·
    refine ⟨9022060684602609078140779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12029414246136812104187705 9022060684602609078140779)
    ·
      refine ⟨13533091026903913617211169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9022060684602609078140779 13533091026903913617211169)
      ·
        refine ⟨10149818270177935212908377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13533091026903913617211169 10149818270177935212908377)
        ·
          refine ⟨7612363702633451409681283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10149818270177935212908377 7612363702633451409681283)
          ·
            refine ⟨11418545553950177114521925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612363702633451409681283 11418545553950177114521925)
            ·
              refine ⟨2140977291365658208972861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11418545553950177114521925 2140977291365658208972861)
              ·
                refine ⟨802866484262121828364823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2140977291365658208972861 802866484262121828364823)
                ·
                  refine ⟨1204299726393182742547235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802866484262121828364823 1204299726393182742547235)
                  ·
                    refine ⟨1806449589589774113820853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1204299726393182742547235 1806449589589774113820853)
                    ·
                      refine ⟨169354649024041323170705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1806449589589774113820853 169354649024041323170705)
                      ·
                        rfl

theorem cell23_329817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_329817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329817 prefixEnd_329817 := by exact prefixLift 329817
  have htrace : WordTrace (prefixWord ++ tailWord_329817) baseStart_329817 baseEnd_329817 := by
    simpa [prefixWord, tailWord_329817, baseEnd_329817] using wordTrace_append hprefix tailTrace_329817
  have hstable : (prefixWord ++ tailWord_329817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329817).length < 2 ^ (prefixWord ++ tailWord_329817).sum := by decide
  have hdescent : baseEnd_329817 < baseStart_329817 := by decide
  rcases family_descends (prefixWord ++ tailWord_329817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329824 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 4, 4]
def baseStart_329824 : Nat := 118140960795 + 329824 * 2 ^ 59
def prefixEnd_329824 : Nat := 4983230072969 + 3 ^ 40 * 329824 * 2
def baseEnd_329824 : Nat := 56452747796207598594391

theorem tailTrace_329824 : CollatzResearch.WordTrace tailWord_329824 prefixEnd_329824 56452747796207598594391 := by
  unfold tailWord_329824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6014834778555726149846263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8019779704740968199795017 6014834778555726149846263)
  ·
    refine ⟨9022252167833589224769395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6014834778555726149846263 9022252167833589224769395)
    ·
      refine ⟨13533378251750383837154093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9022252167833589224769395 13533378251750383837154093)
      ·
        refine ⟨5075016844406393938932785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13533378251750383837154093 5075016844406393938932785)
        ·
          refine ⟨3806262633304795454199589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5075016844406393938932785 3806262633304795454199589)
          ·
            refine ⟨713674243744649147662423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3806262633304795454199589 713674243744649147662423)
            ·
              refine ⟨1070511365616973721493635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713674243744649147662423 1070511365616973721493635)
              ·
                refine ⟨1605767048425460582240453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070511365616973721493635 1605767048425460582240453)
                ·
                  refine ⟨301081321579773859170085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605767048425460582240453 301081321579773859170085)
                  ·
                    refine ⟨56452747796207598594391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301081321579773859170085 56452747796207598594391)
                    ·
                      rfl

theorem cell23_329824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_329824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329824 prefixEnd_329824 := by exact prefixLift 329824
  have htrace : WordTrace (prefixWord ++ tailWord_329824) baseStart_329824 baseEnd_329824 := by
    simpa [prefixWord, tailWord_329824, baseEnd_329824] using wordTrace_append hprefix tailTrace_329824
  have hstable : (prefixWord ++ tailWord_329824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329824).length < 2 ^ (prefixWord ++ tailWord_329824).sum := by decide
  have hdescent : baseEnd_329824 < baseStart_329824 := by decide
  rcases family_descends (prefixWord ++ tailWord_329824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329827 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4]
def baseStart_329827 : Nat := 118140960795 + 329827 * 2 ^ 59
def prefixEnd_329827 : Nat := 4983230072969 + 3 ^ 40 * 329827 * 2
def baseEnd_329827 : Nat := 169359783830586284045659

theorem tailTrace_329827 : CollatzResearch.WordTrace tailWord_329827 prefixEnd_329827 169359783830586284045659 := by
  unfold tailWord_329827
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029778976100583812051735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8019852650733722541367823 12029778976100583812051735)
  ·
    refine ⟨18044668464150875718077603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12029778976100583812051735 18044668464150875718077603)
    ·
      refine ⟨27067002696226313577116405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18044668464150875718077603 27067002696226313577116405)
      ·
        refine ⟨2537531502771216897854663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27067002696226313577116405 2537531502771216897854663)
        ·
          refine ⟨3806297254156825346781995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537531502771216897854663 3806297254156825346781995)
          ·
            refine ⟨5709445881235238020172993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806297254156825346781995 5709445881235238020172993)
            ·
              refine ⟨4282084410926428515129745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5709445881235238020172993 4282084410926428515129745)
              ·
                refine ⟨3211563308194821386347309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282084410926428515129745 3211563308194821386347309)
                ·
                  refine ⟨1204336240573058019880241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3211563308194821386347309 1204336240573058019880241)
                  ·
                    refine ⟨903252180429793514910181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1204336240573058019880241 903252180429793514910181)
                    ·
                      refine ⟨169359783830586284045659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 903252180429793514910181 169359783830586284045659)
                      ·
                        rfl

theorem cell23_329827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_329827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329827 prefixEnd_329827 := by exact prefixLift 329827
  have htrace : WordTrace (prefixWord ++ tailWord_329827) baseStart_329827 baseEnd_329827 := by
    simpa [prefixWord, tailWord_329827, baseEnd_329827] using wordTrace_append hprefix tailTrace_329827
  have hstable : (prefixWord ++ tailWord_329827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329827).length < 2 ^ (prefixWord ++ tailWord_329827).sum := by decide
  have hdescent : baseEnd_329827 < baseStart_329827 := by decide
  rcases family_descends (prefixWord ++ tailWord_329827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329837 : List Nat := [1, 5, 1, 1, 2, 1, 2, 10]
def baseStart_329837 : Nat := 118140960795 + 329837 * 2 ^ 59
def prefixEnd_329837 : Nat := 4983230072969 + 3 ^ 40 * 329837 * 2
def baseEnd_329837 : Nat := 6272774764338194256319

theorem tailTrace_329837 : CollatzResearch.WordTrace tailWord_329837 prefixEnd_329837 6272774764338194256319 := by
  unfold tailWord_329837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030143706064355519915765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8020095804042903679943843 12030143706064355519915765)
  ·
    refine ⟨1127825972443533329992103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12030143706064355519915765 1127825972443533329992103)
    ·
      refine ⟨1691738958665299994988155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127825972443533329992103 1691738958665299994988155)
      ·
        refine ⟨2537608437997949992482233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691738958665299994988155 2537608437997949992482233)
        ·
          refine ⟨1903206328498462494361675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2537608437997949992482233 1903206328498462494361675)
          ·
            refine ⟨2854809492747693741542513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903206328498462494361675 2854809492747693741542513)
            ·
              refine ⟨2141107119560770306156885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854809492747693741542513 2141107119560770306156885)
              ·
                refine ⟨6272774764338194256319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2141107119560770306156885 6272774764338194256319)
                ·
                  rfl

theorem cell23_329837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 10].length) (baseStart_329837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329837 prefixEnd_329837 := by exact prefixLift 329837
  have htrace : WordTrace (prefixWord ++ tailWord_329837) baseStart_329837 baseEnd_329837 := by
    simpa [prefixWord, tailWord_329837, baseEnd_329837] using wordTrace_append hprefix tailTrace_329837
  have hstable : (prefixWord ++ tailWord_329837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329837).length < 2 ^ (prefixWord ++ tailWord_329837).sum := by decide
  have hdescent : baseEnd_329837 < baseStart_329837 := by decide
  rcases family_descends (prefixWord ++ tailWord_329837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329841 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 2, 4]
def baseStart_329841 : Nat := 118140960795 + 329841 * 2 ^ 59
def prefixEnd_329841 : Nat := 4983230072969 + 3 ^ 40 * 329841 * 2
def baseEnd_329841 : Nat := 56455657519916409756865

theorem tailTrace_329841 : CollatzResearch.WordTrace tailWord_329841 prefixEnd_329841 56455657519916409756865 := by
  unfold tailWord_329841
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030289598049864203061377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8020193065366576135374251 12030289598049864203061377)
  ·
    refine ⟨9022717198537398152296033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12030289598049864203061377 9022717198537398152296033)
    ·
      refine ⟨6767037898903048614222025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9022717198537398152296033 6767037898903048614222025)
      ·
        refine ⟨5075278424177286460666519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6767037898903048614222025 5075278424177286460666519)
        ·
          refine ⟨7612917636265929690999779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075278424177286460666519 7612917636265929690999779)
          ·
            refine ⟨11419376454398894536499669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612917636265929690999779 11419376454398894536499669)
            ·
              refine ⟨267641635649974090699211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11419376454398894536499669 267641635649974090699211)
              ·
                refine ⟨401462453474961136048817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267641635649974090699211 401462453474961136048817)
                ·
                  refine ⟨301096840106220852036613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401462453474961136048817 301096840106220852036613)
                  ·
                    refine ⟨56455657519916409756865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301096840106220852036613 56455657519916409756865)
                    ·
                      rfl

theorem cell23_329841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_329841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329841 prefixEnd_329841 := by exact prefixLift 329841
  have htrace : WordTrace (prefixWord ++ tailWord_329841) baseStart_329841 baseEnd_329841 := by
    simpa [prefixWord, tailWord_329841, baseEnd_329841] using wordTrace_append hprefix tailTrace_329841
  have hstable : (prefixWord ++ tailWord_329841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329841).length < 2 ^ (prefixWord ++ tailWord_329841).sum := by decide
  have hdescent : baseEnd_329841 < baseStart_329841 := by decide
  rcases family_descends (prefixWord ++ tailWord_329841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329877 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_329877 : Nat := 118140960795 + 329877 * 2 ^ 59
def prefixEnd_329877 : Nat := 4983230072969 + 3 ^ 40 * 329877 * 2
def baseEnd_329877 : Nat := 169385457863311088420429

theorem tailTrace_329877 : CollatzResearch.WordTrace tailWord_329877 prefixEnd_329877 169385457863311088420429 := by
  unfold tailWord_329877
  simp only [CollatzResearch.WordTrace]
  refine ⟨12031602625919442351371885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8021068417279628234247923 12031602625919442351371885)
  ·
    refine ⟨4511850984719790881764457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12031602625919442351371885 4511850984719790881764457)
    ·
      refine ⟨3383888238539843161323343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4511850984719790881764457 3383888238539843161323343)
      ·
        refine ⟨5075832357809764741985015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383888238539843161323343 5075832357809764741985015)
        ·
          refine ⟨7613748536714647112977523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075832357809764741985015 7613748536714647112977523)
          ·
            refine ⟨11420622805071970669466285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7613748536714647112977523 11420622805071970669466285)
            ·
              refine ⟨4282733551901989001049857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11420622805071970669466285 4282733551901989001049857)
              ·
                refine ⟨3212050163926491750787393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282733551901989001049857 3212050163926491750787393)
                ·
                  refine ⟨2409037622944868813090545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3212050163926491750787393 2409037622944868813090545)
                  ·
                    refine ⟨1806778217208651609817909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2409037622944868813090545 1806778217208651609817909)
                    ·
                      refine ⟨169385457863311088420429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1806778217208651609817909 169385457863311088420429)
                      ·
                        rfl

theorem cell23_329877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_329877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329877 prefixEnd_329877 := by exact prefixLift 329877
  have htrace : WordTrace (prefixWord ++ tailWord_329877) baseStart_329877 baseEnd_329877 := by
    simpa [prefixWord, tailWord_329877, baseEnd_329877] using wordTrace_append hprefix tailTrace_329877
  have hstable : (prefixWord ++ tailWord_329877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329877).length < 2 ^ (prefixWord ++ tailWord_329877).sum := by decide
  have hdescent : baseEnd_329877 < baseStart_329877 := by decide
  rcases family_descends (prefixWord ++ tailWord_329877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329882 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2]
def baseStart_329882 : Nat := 118140960795 + 329882 * 2 ^ 59
def prefixEnd_329882 : Nat := 4983230072969 + 3 ^ 40 * 329882 * 2
def baseEnd_329882 : Nat := 169388025266583568857907

theorem tailTrace_329882 : CollatzResearch.WordTrace tailWord_329882 prefixEnd_329882 169388025266583568857907 := by
  unfold tailWord_329882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007946247725332051325975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8021189993934218803535933 3007946247725332051325975)
  ·
    refine ⟨4511919371587998076988963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3007946247725332051325975 4511919371587998076988963)
    ·
      refine ⟨6767879057381997115483445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4511919371587998076988963 6767879057381997115483445)
      ·
        refine ⟨634488661629562229576573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6767879057381997115483445 634488661629562229576573)
        ·
          refine ⟨237933248111085836091215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 634488661629562229576573 237933248111085836091215)
          ·
            refine ⟨356899872166628754136823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237933248111085836091215 356899872166628754136823)
            ·
              refine ⟨535349808249943131205235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356899872166628754136823 535349808249943131205235)
              ·
                refine ⟨803024712374914696807853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535349808249943131205235 803024712374914696807853)
                ·
                  refine ⟨301134267140593011302945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803024712374914696807853 301134267140593011302945)
                  ·
                    refine ⟨225850700355444758477209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301134267140593011302945 225850700355444758477209)
                    ·
                      refine ⟨169388025266583568857907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225850700355444758477209 169388025266583568857907)
                      ·
                        rfl

theorem cell23_329882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_329882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329882 prefixEnd_329882 := by exact prefixLift 329882
  have htrace : WordTrace (prefixWord ++ tailWord_329882) baseStart_329882 baseEnd_329882 := by
    simpa [prefixWord, tailWord_329882, baseEnd_329882] using wordTrace_append hprefix tailTrace_329882
  have hstable : (prefixWord ++ tailWord_329882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329882).length < 2 ^ (prefixWord ++ tailWord_329882).sum := by decide
  have hdescent : baseEnd_329882 < baseStart_329882 := by decide
  rcases family_descends (prefixWord ++ tailWord_329882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329902 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_329902 : Nat := 118140960795 + 329902 * 2 ^ 59
def prefixEnd_329902 : Nat := 4983230072969 + 3 ^ 40 * 329902 * 2
def baseEnd_329902 : Nat := 169398294879673490607815

theorem tailTrace_329902 : CollatzResearch.WordTrace tailWord_329902 prefixEnd_329902 169398294879673490607815 := by
  unfold tailWord_329902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504064306353608952628995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8021676300552581080687973 1504064306353608952628995)
  ·
    refine ⟨2256096459530413428943493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504064306353608952628995 2256096459530413428943493)
    ·
      refine ⟨423018086161952517926905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2256096459530413428943493 423018086161952517926905)
      ·
        refine ⟨317263564621464388445179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423018086161952517926905 317263564621464388445179)
        ·
          refine ⟨475895346932196582667769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317263564621464388445179 475895346932196582667769)
          ·
            refine ⟨356921510199147437000827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 475895346932196582667769 356921510199147437000827)
            ·
              refine ⟨535382265298721155501241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356921510199147437000827 535382265298721155501241)
              ·
                refine ⟨401536698974040866625931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535382265298721155501241 401536698974040866625931)
                ·
                  refine ⟨602305048461061299938897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401536698974040866625931 602305048461061299938897)
                  ·
                    refine ⟨451728786345795974954173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 602305048461061299938897 451728786345795974954173)
                    ·
                      refine ⟨169398294879673490607815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 451728786345795974954173 169398294879673490607815)
                      ·
                        rfl

theorem cell23_329902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_329902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329902 prefixEnd_329902 := by exact prefixLift 329902
  have htrace : WordTrace (prefixWord ++ tailWord_329902) baseStart_329902 baseEnd_329902 := by
    simpa [prefixWord, tailWord_329902, baseEnd_329902] using wordTrace_append hprefix tailTrace_329902
  have hstable : (prefixWord ++ tailWord_329902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329902).length < 2 ^ (prefixWord ++ tailWord_329902).sum := by decide
  have hdescent : baseEnd_329902 < baseStart_329902 := by decide
  rcases family_descends (prefixWord ++ tailWord_329902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329937 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_329937 : Nat := 118140960795 + 329937 * 2 ^ 59
def prefixEnd_329937 : Nat := 4983230072969 + 3 ^ 40 * 329937 * 2
def baseEnd_329937 : Nat := 169416266702580853670153

theorem tailTrace_329937 : CollatzResearch.WordTrace tailWord_329937 prefixEnd_329937 169416266702580853670153 := by
  unfold tailWord_329937
  simp only [CollatzResearch.WordTrace]
  refine ⟨12033791005702072598556065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8022527337134715065704043 12033791005702072598556065)
  ·
    refine ⟨9025343254276554448917049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12033791005702072598556065 9025343254276554448917049)
    ·
      refine ⟨6769007440707415836687787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9025343254276554448917049 6769007440707415836687787)
      ·
        refine ⟨10153511161061123755031681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6769007440707415836687787 10153511161061123755031681)
        ·
          refine ⟨7615133370795842816273761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10153511161061123755031681 7615133370795842816273761)
          ·
            refine ⟨5711350028096882112205321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7615133370795842816273761 5711350028096882112205321)
            ·
              refine ⟨4283512521072661584153991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5711350028096882112205321 4283512521072661584153991)
              ·
                refine ⟨6425268781608992376230987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283512521072661584153991 6425268781608992376230987)
                ·
                  refine ⟨9637903172413488564346481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425268781608992376230987 9637903172413488564346481)
                  ·
                    refine ⟨7228427379310116423259861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9637903172413488564346481 7228427379310116423259861)
                    ·
                      refine ⟨169416266702580853670153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7228427379310116423259861 169416266702580853670153)
                      ·
                        rfl

theorem cell23_329937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_329937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329937 prefixEnd_329937 := by exact prefixLift 329937
  have htrace : WordTrace (prefixWord ++ tailWord_329937) baseStart_329937 baseEnd_329937 := by
    simpa [prefixWord, tailWord_329937, baseEnd_329937] using wordTrace_append hprefix tailTrace_329937
  have hstable : (prefixWord ++ tailWord_329937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329937).length < 2 ^ (prefixWord ++ tailWord_329937).sum := by decide
  have hdescent : baseEnd_329937 < baseStart_329937 := by decide
  rcases family_descends (prefixWord ++ tailWord_329937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329948 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_329948 : Nat := 118140960795 + 329948 * 2 ^ 59
def prefixEnd_329948 : Nat := 4983230072969 + 3 ^ 40 * 329948 * 2
def baseEnd_329948 : Nat := 56473971663260103544201

theorem tailTrace_329948 : CollatzResearch.WordTrace tailWord_329948 prefixEnd_329948 56473971663260103544201 := by
  unfold tailWord_329948
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017096104331110738603249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8022794805774814318137665 6017096104331110738603249)
  ·
    refine ⟨4512822078248333053952437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6017096104331110738603249 4512822078248333053952437)
    ·
      refine ⟨423077069835781223808041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4512822078248333053952437 423077069835781223808041)
      ·
        refine ⟨317307802376835917856031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 423077069835781223808041 317307802376835917856031)
        ·
          refine ⟨475961703565253876784047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317307802376835917856031 475961703565253876784047)
          ·
            refine ⟨713942555347880815176071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475961703565253876784047 713942555347880815176071)
            ·
              refine ⟨1070913833021821222764107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713942555347880815176071 1070913833021821222764107)
              ·
                refine ⟨1606370749532731834146161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070913833021821222764107 1606370749532731834146161)
                ·
                  refine ⟨1204778062149548875609621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1606370749532731834146161 1204778062149548875609621)
                  ·
                    refine ⟨56473971663260103544201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1204778062149548875609621 56473971663260103544201)
                    ·
                      rfl

theorem cell23_329948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_329948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329948 prefixEnd_329948 := by exact prefixLift 329948
  have htrace : WordTrace (prefixWord ++ tailWord_329948) baseStart_329948 baseEnd_329948 := by
    simpa [prefixWord, tailWord_329948, baseEnd_329948] using wordTrace_append hprefix tailTrace_329948
  have hstable : (prefixWord ++ tailWord_329948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329948).length < 2 ^ (prefixWord ++ tailWord_329948).sum := by decide
  have hdescent : baseEnd_329948 < baseStart_329948 := by decide
  rcases family_descends (prefixWord ++ tailWord_329948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_329955 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 1, 4, 2]
def baseStart_329955 : Nat := 118140960795 + 329955 * 2 ^ 59
def prefixEnd_329955 : Nat := 4983230072969 + 3 ^ 40 * 329955 * 2
def baseEnd_329955 : Nat := 169425509354361783245071

theorem tailTrace_329955 : CollatzResearch.WordTrace tailWord_329955 prefixEnd_329955 169425509354361783245071 := by
  unfold tailWord_329955
  simp only [CollatzResearch.WordTrace]
  refine ⟨12034447519636861672711319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8022965013091241115140879 12034447519636861672711319)
  ·
    refine ⟨18051671279455292509066979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12034447519636861672711319 18051671279455292509066979)
    ·
      refine ⟨27077506919182938763600469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18051671279455292509066979 27077506919182938763600469)
      ·
        refine ⟨317314534209175063635943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 27077506919182938763600469 317314534209175063635943)
        ·
          refine ⟨475971801313762595453915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317314534209175063635943 475971801313762595453915)
          ·
            refine ⟨713957701970643893180873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475971801313762595453915 713957701970643893180873)
            ·
              refine ⟨535468276477982919885655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713957701970643893180873 535468276477982919885655)
              ·
                refine ⟨803202414716974379828483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535468276477982919885655 803202414716974379828483)
                ·
                  refine ⟨1204803622075461569742725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803202414716974379828483 1204803622075461569742725)
                  ·
                    refine ⟨225900679139149044326761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1204803622075461569742725 225900679139149044326761)
                    ·
                      refine ⟨169425509354361783245071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225900679139149044326761 169425509354361783245071)
                      ·
                        rfl

theorem cell23_329955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_329955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_329955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_329955 prefixEnd_329955 := by exact prefixLift 329955
  have htrace : WordTrace (prefixWord ++ tailWord_329955) baseStart_329955 baseEnd_329955 := by
    simpa [prefixWord, tailWord_329955, baseEnd_329955] using wordTrace_append hprefix tailTrace_329955
  have hstable : (prefixWord ++ tailWord_329955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_329955).length < 2 ^ (prefixWord ++ tailWord_329955).sum := by decide
  have hdescent : baseEnd_329955 < baseStart_329955 := by decide
  rcases family_descends (prefixWord ++ tailWord_329955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330011 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 2, 4, 2]
def baseStart_330011 : Nat := 118140960795 + 330011 * 2 ^ 59
def prefixEnd_330011 : Nat := 4983230072969 + 3 ^ 40 * 330011 * 2
def baseEnd_330011 : Nat := 169454264271013564144813

theorem tailTrace_330011 : CollatzResearch.WordTrace tailWord_330011 prefixEnd_330011 169454264271013564144813 := by
  unfold tailWord_330011
  simp only [CollatzResearch.WordTrace]
  refine ⟨12036490007433983236749887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8024326671622655491166591 12036490007433983236749887)
  ·
    refine ⟨18054735011150974855124831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12036490007433983236749887 18054735011150974855124831)
    ·
      refine ⟨27082102516726462282687247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18054735011150974855124831 27082102516726462282687247)
      ·
        refine ⟨40623153775089693424030871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27082102516726462282687247 40623153775089693424030871)
        ·
          refine ⟨60934730662634540136046307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40623153775089693424030871 60934730662634540136046307)
          ·
            refine ⟨91402095993951810204069461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60934730662634540136046307 91402095993951810204069461)
            ·
              refine ⟨1071118312429122775828939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 91402095993951810204069461 1071118312429122775828939)
              ·
                refine ⟨1606677468643684163743409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071118312429122775828939 1606677468643684163743409)
                ·
                  refine ⟨1205008101482763122807557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1606677468643684163743409 1205008101482763122807557)
                  ·
                    refine ⟨225939019028018085526417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205008101482763122807557 225939019028018085526417)
                    ·
                      refine ⟨169454264271013564144813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 225939019028018085526417 169454264271013564144813)
                      ·
                        rfl

theorem cell23_330011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 4, 2].length) (baseStart_330011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330011 prefixEnd_330011 := by exact prefixLift 330011
  have htrace : WordTrace (prefixWord ++ tailWord_330011) baseStart_330011 baseEnd_330011 := by
    simpa [prefixWord, tailWord_330011, baseEnd_330011] using wordTrace_append hprefix tailTrace_330011
  have hstable : (prefixWord ++ tailWord_330011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330011).length < 2 ^ (prefixWord ++ tailWord_330011).sum := by decide
  have hdescent : baseEnd_330011 < baseStart_330011 := by decide
  rcases family_descends (prefixWord ++ tailWord_330011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330055 : List Nat := [1, 1, 4, 1, 2, 2, 5, 2, 1, 4]
def baseStart_330055 : Nat := 118140960795 + 330055 * 2 ^ 59
def prefixEnd_330055 : Nat := 4983230072969 + 3 ^ 40 * 330055 * 2
def baseEnd_330055 : Nat := 56492285806603797331537

theorem tailTrace_330055 : CollatzResearch.WordTrace tailWord_330055 prefixEnd_330055 56492285806603797331537 := by
  unfold tailWord_330055
  simp only [CollatzResearch.WordTrace]
  refine ⟨12038094819274578751351619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8025396546183052500901079 12038094819274578751351619)
  ·
    refine ⟨18057142228911868127027429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12038094819274578751351619 18057142228911868127027429)
    ·
      refine ⟨3385714167920975273817643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18057142228911868127027429 3385714167920975273817643)
      ·
        refine ⟨5078571251881462910726465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3385714167920975273817643 5078571251881462910726465)
        ·
          refine ⟨3808928438911097183044849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5078571251881462910726465 3808928438911097183044849)
          ·
            refine ⟨2856696329183322887283637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3808928438911097183044849 2856696329183322887283637)
            ·
              refine ⟨267815280860936520682841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2856696329183322887283637 267815280860936520682841)
              ·
                refine ⟨200861460645702390512131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267815280860936520682841 200861460645702390512131)
                ·
                  refine ⟨301292190968553585768197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200861460645702390512131 301292190968553585768197)
                  ·
                    refine ⟨56492285806603797331537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301292190968553585768197 56492285806603797331537)
                    ·
                      rfl

theorem cell23_330055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_330055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330055 prefixEnd_330055 := by exact prefixLift 330055
  have htrace : WordTrace (prefixWord ++ tailWord_330055) baseStart_330055 baseEnd_330055 := by
    simpa [prefixWord, tailWord_330055, baseEnd_330055] using wordTrace_append hprefix tailTrace_330055
  have hstable : (prefixWord ++ tailWord_330055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330055).length < 2 ^ (prefixWord ++ tailWord_330055).sum := by decide
  have hdescent : baseEnd_330055 < baseStart_330055 := by decide
  rcases family_descends (prefixWord ++ tailWord_330055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330068 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 6]
def baseStart_330068 : Nat := 118140960795 + 330068 * 2 ^ 59
def prefixEnd_330068 : Nat := 4983230072969 + 3 ^ 40 * 330068 * 2
def baseEnd_330068 : Nat := 18831503629813315681339

theorem tailTrace_330068 : CollatzResearch.WordTrace tailWord_330068 prefixEnd_330068 18831503629813315681339 := by
  unfold tailWord_330068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6019284484113740985787429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8025712645484987981049905 6019284484113740985787429)
  ·
    refine ⟨1128615840771326434835143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6019284484113740985787429 1128615840771326434835143)
    ·
      refine ⟨1692923761156989652252715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128615840771326434835143 1692923761156989652252715)
      ·
        refine ⟨2539385641735484478379073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692923761156989652252715 2539385641735484478379073)
        ·
          refine ⟨1904539231301613358784305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2539385641735484478379073 1904539231301613358784305)
          ·
            refine ⟨1428404423476210019088229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904539231301613358784305 1428404423476210019088229)
            ·
              refine ⟨267825829401789378579043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1428404423476210019088229 267825829401789378579043)
              ·
                refine ⟨401738744102684067868565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267825829401789378579043 401738744102684067868565)
                ·
                  refine ⟨18831503629813315681339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 401738744102684067868565 18831503629813315681339)
                  ·
                    rfl

theorem cell23_330068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_330068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330068 prefixEnd_330068 := by exact prefixLift 330068
  have htrace : WordTrace (prefixWord ++ tailWord_330068) baseStart_330068 baseEnd_330068 := by
    simpa [prefixWord, tailWord_330068, baseEnd_330068] using wordTrace_append hprefix tailTrace_330068
  have hstable : (prefixWord ++ tailWord_330068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330068).length < 2 ^ (prefixWord ++ tailWord_330068).sum := by decide
  have hdescent : baseEnd_330068 < baseStart_330068 := by decide
  rcases family_descends (prefixWord ++ tailWord_330068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330138 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_330138 : Nat := 118140960795 + 330138 * 2 ^ 59
def prefixEnd_330138 : Nat := 4983230072969 + 3 ^ 40 * 330138 * 2
def baseEnd_330138 : Nat := 169519476314134567256729

theorem tailTrace_330138 : CollatzResearch.WordTrace tailWord_330138 prefixEnd_330138 169519476314134567256729 := by
  unfold tailWord_330138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010280519493470981655767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8027414718649255951082045 3010280519493470981655767)
  ·
    refine ⟨4515420779240206472483651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010280519493470981655767 4515420779240206472483651)
    ·
      refine ⟨6773131168860309708725477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515420779240206472483651 6773131168860309708725477)
      ·
        refine ⟨1269962094161308070386027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6773131168860309708725477 1269962094161308070386027)
        ·
          refine ⟨1904943141241962105579041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269962094161308070386027 1904943141241962105579041)
          ·
            refine ⟨1428707355931471579184281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904943141241962105579041 1428707355931471579184281)
            ·
              refine ⟨1071530516948603684388211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428707355931471579184281 1071530516948603684388211)
              ·
                refine ⟨1607295775422905526582317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071530516948603684388211 1607295775422905526582317)
                ·
                  refine ⟨602735915783589572468369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1607295775422905526582317 602735915783589572468369)
                  ·
                    refine ⟨452051936837692179351277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 602735915783589572468369 452051936837692179351277)
                    ·
                      refine ⟨169519476314134567256729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 452051936837692179351277 169519476314134567256729)
                      ·
                        rfl

theorem cell23_330138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_330138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330138 prefixEnd_330138 := by exact prefixLift 330138
  have htrace : WordTrace (prefixWord ++ tailWord_330138) baseStart_330138 baseEnd_330138 := by
    simpa [prefixWord, tailWord_330138, baseEnd_330138] using wordTrace_append hprefix tailTrace_330138
  have hstable : (prefixWord ++ tailWord_330138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330138).length < 2 ^ (prefixWord ++ tailWord_330138).sum := by decide
  have hdescent : baseEnd_330138 < baseStart_330138 := by decide
  rcases family_descends (prefixWord ++ tailWord_330138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330152 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_330152 : Nat := 118140960795 + 330152 * 2 ^ 59
def prefixEnd_330152 : Nat := 4983230072969 + 3 ^ 40 * 330152 * 2
def baseEnd_330152 : Nat := 169526665043297512481665

theorem tailTrace_330152 : CollatzResearch.WordTrace tailWord_330152 prefixEnd_330152 169526665043297512481665 := by
  unfold tailWord_330152
  simp only [CollatzResearch.WordTrace]
  refine ⟨6020816349961582158816355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8027755133282109545088473 6020816349961582158816355)
  ·
    refine ⟨9031224524942373238224533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6020816349961582158816355 9031224524942373238224533)
    ·
      refine ⟨423338649606673745541775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9031224524942373238224533 423338649606673745541775)
      ·
        refine ⟨635007974410010618312663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423338649606673745541775 635007974410010618312663)
        ·
          refine ⟨952511961615015927468995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635007974410010618312663 952511961615015927468995)
          ·
            refine ⟨1428767942422523891203493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952511961615015927468995 1428767942422523891203493)
            ·
              refine ⟨267893989204223229600655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1428767942422523891203493 267893989204223229600655)
              ·
                refine ⟨401840983806334844400983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267893989204223229600655 401840983806334844400983)
                ·
                  refine ⟨602761475709502266601475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401840983806334844400983 602761475709502266601475)
                  ·
                    refine ⟨904142213564253399902213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 602761475709502266601475 904142213564253399902213)
                    ·
                      refine ⟨169526665043297512481665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 904142213564253399902213 169526665043297512481665)
                      ·
                        rfl

theorem cell23_330152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_330152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330152 prefixEnd_330152 := by exact prefixLift 330152
  have htrace : WordTrace (prefixWord ++ tailWord_330152) baseStart_330152 baseEnd_330152 := by
    simpa [prefixWord, tailWord_330152, baseEnd_330152] using wordTrace_append hprefix tailTrace_330152
  have hstable : (prefixWord ++ tailWord_330152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330152).length < 2 ^ (prefixWord ++ tailWord_330152).sum := by decide
  have hdescent : baseEnd_330152 < baseStart_330152 := by decide
  rcases family_descends (prefixWord ++ tailWord_330152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330198 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_330198 : Nat := 118140960795 + 330198 * 2 ^ 59
def prefixEnd_330198 : Nat := 4983230072969 + 3 ^ 40 * 330198 * 2
def baseEnd_330198 : Nat := 169550285153404332506453

theorem tailTrace_330198 : CollatzResearch.WordTrace tailWord_330198 prefixEnd_330198 169550285153404332506453 := by
  unfold tailWord_330198
  simp only [CollatzResearch.WordTrace]
  refine ⟨752706903609782135862953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8028873638504342782538165 752706903609782135862953)
  ·
    refine ⟨564530177707336601897215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 752706903609782135862953 564530177707336601897215)
    ·
      refine ⟨846795266561004902845823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564530177707336601897215 846795266561004902845823)
      ·
        refine ⟨1270192899841507354268735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846795266561004902845823 1270192899841507354268735)
        ·
          refine ⟨1905289349762261031403103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270192899841507354268735 1905289349762261031403103)
          ·
            refine ⟨2857934024643391547104655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905289349762261031403103 2857934024643391547104655)
            ·
              refine ⟨4286901036965087320656983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857934024643391547104655 4286901036965087320656983)
              ·
                refine ⟨6430351555447630980985475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286901036965087320656983 6430351555447630980985475)
                ·
                  refine ⟨9645527333171446471478213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6430351555447630980985475 9645527333171446471478213)
                  ·
                    refine ⟨1808536374969646213402165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9645527333171446471478213 1808536374969646213402165)
                    ·
                      refine ⟨169550285153404332506453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1808536374969646213402165 169550285153404332506453)
                      ·
                        rfl

theorem cell23_330198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_330198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330198 prefixEnd_330198 := by exact prefixLift 330198
  have htrace : WordTrace (prefixWord ++ tailWord_330198) baseStart_330198 baseEnd_330198 := by
    simpa [prefixWord, tailWord_330198, baseEnd_330198] using wordTrace_append hprefix tailTrace_330198
  have hstable : (prefixWord ++ tailWord_330198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330198).length < 2 ^ (prefixWord ++ tailWord_330198).sum := by decide
  have hdescent : baseEnd_330198 < baseStart_330198 := by decide
  rcases family_descends (prefixWord ++ tailWord_330198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330208 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 3, 4, 2]
def baseStart_330208 : Nat := 118140960795 + 330208 * 2 ^ 59
def prefixEnd_330208 : Nat := 4983230072969 + 3 ^ 40 * 330208 * 2
def baseEnd_330208 : Nat := 169555419959949293381407

theorem tailTrace_330208 : CollatzResearch.WordTrace tailWord_330208 prefixEnd_330208 169555419959949293381407 := by
  unfold tailWord_330208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6021837593860142940835639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8029116791813523921114185 6021837593860142940835639)
  ·
    refine ⟨9032756390790214411253459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6021837593860142940835639 9032756390790214411253459)
    ·
      refine ⟨13549134586185321616880189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9032756390790214411253459 13549134586185321616880189)
      ·
        refine ⟨5080925469819495606330071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13549134586185321616880189 5080925469819495606330071)
        ·
          refine ⟨7621388204729243409495107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5080925469819495606330071 7621388204729243409495107)
          ·
            refine ⟨11432082307093865114242661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7621388204729243409495107 11432082307093865114242661)
            ·
              refine ⟨2143515432580099708920499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11432082307093865114242661 2143515432580099708920499)
              ·
                refine ⟨3215273148870149563380749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143515432580099708920499 3215273148870149563380749)
                ·
                  refine ⟨1205727430826306086267781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3215273148870149563380749 1205727430826306086267781)
                  ·
                    refine ⟨226073893279932391175209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1205727430826306086267781 226073893279932391175209)
                    ·
                      refine ⟨169555419959949293381407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226073893279932391175209 169555419959949293381407)
                      ·
                        rfl

theorem cell23_330208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_330208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330208 prefixEnd_330208 := by exact prefixLift 330208
  have htrace : WordTrace (prefixWord ++ tailWord_330208) baseStart_330208 baseEnd_330208 := by
    simpa [prefixWord, tailWord_330208, baseEnd_330208] using wordTrace_append hprefix tailTrace_330208
  have hstable : (prefixWord ++ tailWord_330208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330208).length < 2 ^ (prefixWord ++ tailWord_330208).sum := by decide
  have hdescent : baseEnd_330208 < baseStart_330208 := by decide
  rcases family_descends (prefixWord ++ tailWord_330208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330225 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 4, 2, 2]
def baseStart_330225 : Nat := 118140960795 + 330225 * 2 ^ 59
def prefixEnd_330225 : Nat := 4983230072969 + 3 ^ 40 * 330225 * 2
def baseEnd_330225 : Nat := 169564149131075726868829

theorem tailTrace_330225 : CollatzResearch.WordTrace tailWord_330225 prefixEnd_330225 169564149131075726868829 := by
  unfold tailWord_330225
  simp only [CollatzResearch.WordTrace]
  refine ⟨12044295228658697785040129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8029530152439131856693419 12044295228658697785040129)
  ·
    refine ⟨9033221421494023338780097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12044295228658697785040129 9033221421494023338780097)
    ·
      refine ⟨6774916066120517504085073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9033221421494023338780097 6774916066120517504085073)
      ·
        refine ⟨5081187049590388128063805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6774916066120517504085073 5081187049590388128063805)
        ·
          refine ⟨1905445143596395548023927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5081187049590388128063805 1905445143596395548023927)
          ·
            refine ⟨2858167715394593322035891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905445143596395548023927 2858167715394593322035891)
            ·
              refine ⟨4287251573091889983053837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858167715394593322035891 4287251573091889983053837)
              ·
                refine ⟨1607719339909458743645189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4287251573091889983053837 1607719339909458743645189)
                ·
                  refine ⟨301447376233023514433473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1607719339909458743645189 301447376233023514433473)
                  ·
                    refine ⟨226085532174767635825105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301447376233023514433473 226085532174767635825105)
                    ·
                      refine ⟨169564149131075726868829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226085532174767635825105 169564149131075726868829)
                      ·
                        rfl

theorem cell23_330225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_330225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330225 prefixEnd_330225 := by exact prefixLift 330225
  have htrace : WordTrace (prefixWord ++ tailWord_330225) baseStart_330225 baseEnd_330225 := by
    simpa [prefixWord, tailWord_330225, baseEnd_330225] using wordTrace_append hprefix tailTrace_330225
  have hstable : (prefixWord ++ tailWord_330225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330225).length < 2 ^ (prefixWord ++ tailWord_330225).sum := by decide
  have hdescent : baseEnd_330225 < baseStart_330225 := by decide
  rcases family_descends (prefixWord ++ tailWord_330225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330246 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_330246 : Nat := 118140960795 + 330246 * 2 ^ 59
def prefixEnd_330246 : Nat := 4983230072969 + 3 ^ 40 * 330246 * 2
def baseEnd_330246 : Nat := 169574932224820144706233

theorem tailTrace_330246 : CollatzResearch.WordTrace tailWord_330246 prefixEnd_330246 169574932224820144706233 := by
  unfold tailWord_330246
  simp only [CollatzResearch.WordTrace]
  refine ⟨376408161299456824111081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8030040774388412247703061 376408161299456824111081)
  ·
    refine ⟨282306120974592618083311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 376408161299456824111081 282306120974592618083311)
    ·
      refine ⟨423459181461888927124967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282306120974592618083311 423459181461888927124967)
      ·
        refine ⟨635188772192833390687451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423459181461888927124967 635188772192833390687451)
        ·
          refine ⟨952783158289250086031177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635188772192833390687451 952783158289250086031177)
          ·
            refine ⟨714587368716937564523383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952783158289250086031177 714587368716937564523383)
            ·
              refine ⟨1071881053075406346785075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714587368716937564523383 1071881053075406346785075)
              ·
                refine ⟨1607821579613109520177613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071881053075406346785075 1607821579613109520177613)
                ·
                  refine ⟨602933092354916070066605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1607821579613109520177613 602933092354916070066605)
                  ·
                    refine ⟨226099909633093526274977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 602933092354916070066605 226099909633093526274977)
                    ·
                      refine ⟨169574932224820144706233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226099909633093526274977 169574932224820144706233)
                      ·
                        rfl

theorem cell23_330246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_330246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330246 prefixEnd_330246 := by exact prefixLift 330246
  have htrace : WordTrace (prefixWord ++ tailWord_330246) baseStart_330246 baseEnd_330246 := by
    simpa [prefixWord, tailWord_330246, baseEnd_330246] using wordTrace_append hprefix tailTrace_330246
  have hstable : (prefixWord ++ tailWord_330246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330246).length < 2 ^ (prefixWord ++ tailWord_330246).sum := by decide
  have hdescent : baseEnd_330246 < baseStart_330246 := by decide
  rcases family_descends (prefixWord ++ tailWord_330246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330276 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_330276 : Nat := 118140960795 + 330276 * 2 ^ 59
def prefixEnd_330276 : Nat := 4983230072969 + 3 ^ 40 * 330276 * 2
def baseEnd_330276 : Nat := 169590336644455027331095

theorem tailTrace_330276 : CollatzResearch.WordTrace tailWord_330276 prefixEnd_330276 169590336644455027331095 := by
  unfold tailWord_330276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6023077675736966747573341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8030770234315955663431121 6023077675736966747573341)
  ·
    refine ⟨2258654128401362530340003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6023077675736966747573341 2258654128401362530340003)
    ·
      refine ⟨3387981192602043795510005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258654128401362530340003 3387981192602043795510005)
      ·
        refine ⟨317623236806441605829063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3387981192602043795510005 317623236806441605829063)
        ·
          refine ⟨476434855209662408743595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317623236806441605829063 476434855209662408743595)
          ·
            refine ⟨714652282814493613115393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476434855209662408743595 714652282814493613115393)
            ·
              refine ⟨535989212110870209836545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714652282814493613115393 535989212110870209836545)
              ·
                refine ⟨401991909083152657377409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535989212110870209836545 401991909083152657377409)
                ·
                  refine ⟨301493931812364493033057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401991909083152657377409 301493931812364493033057)
                  ·
                    refine ⟨226120448859273369774793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301493931812364493033057 226120448859273369774793)
                    ·
                      refine ⟨169590336644455027331095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226120448859273369774793 169590336644455027331095)
                      ·
                        rfl

theorem cell23_330276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_330276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330276 prefixEnd_330276 := by exact prefixLift 330276
  have htrace : WordTrace (prefixWord ++ tailWord_330276) baseStart_330276 baseEnd_330276 := by
    simpa [prefixWord, tailWord_330276, baseEnd_330276] using wordTrace_append hprefix tailTrace_330276
  have hstable : (prefixWord ++ tailWord_330276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330276).length < 2 ^ (prefixWord ++ tailWord_330276).sum := by decide
  have hdescent : baseEnd_330276 < baseStart_330276 := by decide
  rcases family_descends (prefixWord ++ tailWord_330276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330282 : List Nat := [3, 1, 4, 1, 1, 2, 4, 2, 5]
def baseStart_330282 : Nat := 118140960795 + 330282 * 2 ^ 59
def prefixEnd_330282 : Nat := 4983230072969 + 3 ^ 40 * 330282 * 2
def baseEnd_330282 : Nat := 18843713058709111539563

theorem tailTrace_330282 : CollatzResearch.WordTrace tailWord_330282 prefixEnd_330282 18843713058709111539563 := by
  unfold tailWord_330282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011593547363049129966275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8030916126301464346576733 3011593547363049129966275)
  ·
    refine ⟨4517390321044573694949413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3011593547363049129966275 4517390321044573694949413)
    ·
      refine ⟨847010685195857567803015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4517390321044573694949413 847010685195857567803015)
      ·
        refine ⟨1270516027793786351704523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847010685195857567803015 1270516027793786351704523)
        ·
          refine ⟨1905774041690679527556785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270516027793786351704523 1905774041690679527556785)
          ·
            refine ⟨1429330531268009645667589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905774041690679527556785 1429330531268009645667589)
            ·
              refine ⟨267999474612751808562673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1429330531268009645667589 267999474612751808562673)
              ·
                refine ⟨200999605959563856422005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267999474612751808562673 200999605959563856422005)
                ·
                  refine ⟨18843713058709111539563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200999605959563856422005 18843713058709111539563)
                  ·
                    rfl

theorem cell23_330282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_330282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330282 prefixEnd_330282 := by exact prefixLift 330282
  have htrace : WordTrace (prefixWord ++ tailWord_330282) baseStart_330282 baseEnd_330282 := by
    simpa [prefixWord, tailWord_330282, baseEnd_330282] using wordTrace_append hprefix tailTrace_330282
  have hstable : (prefixWord ++ tailWord_330282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330282).length < 2 ^ (prefixWord ++ tailWord_330282).sum := by decide
  have hdescent : baseEnd_330282 < baseStart_330282 := by decide
  rcases family_descends (prefixWord ++ tailWord_330282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330375 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_330375 : Nat := 118140960795 + 330375 * 2 ^ 59
def prefixEnd_330375 : Nat := 4983230072969 + 3 ^ 40 * 330375 * 2
def baseEnd_330375 : Nat := 169641171229250139993139

theorem tailTrace_330375 : CollatzResearch.WordTrace tailWord_330375 prefixEnd_330375 169641171229250139993139 := by
  unfold tailWord_330375
  simp only [CollatzResearch.WordTrace]
  refine ⟨12049766178115273403000579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8033177452076848935333719 12049766178115273403000579)
  ·
    refine ⟨18074649267172910104500869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12049766178115273403000579 18074649267172910104500869)
    ·
      refine ⟨3388996737594920644593913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18074649267172910104500869 3388996737594920644593913)
      ·
        refine ⟨2541747553196190483445435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3388996737594920644593913 2541747553196190483445435)
        ·
          refine ⟨3812621329794285725168153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541747553196190483445435 3812621329794285725168153)
          ·
            refine ⟨2859465997345714293876115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3812621329794285725168153 2859465997345714293876115)
            ·
              refine ⟨4289198996018571440814173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859465997345714293876115 4289198996018571440814173)
              ·
                refine ⟨1608449623506964290305315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4289198996018571440814173 1608449623506964290305315)
                ·
                  refine ⟨2412674435260446435457973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608449623506964290305315 2412674435260446435457973)
                  ·
                    refine ⟨226188228305666853324185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2412674435260446435457973 226188228305666853324185)
                    ·
                      refine ⟨169641171229250139993139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226188228305666853324185 169641171229250139993139)
                      ·
                        rfl

theorem cell23_330375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_330375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330375 prefixEnd_330375 := by exact prefixLift 330375
  have htrace : WordTrace (prefixWord ++ tailWord_330375) baseStart_330375 baseEnd_330375 := by
    simpa [prefixWord, tailWord_330375, baseEnd_330375] using wordTrace_append hprefix tailTrace_330375
  have hstable : (prefixWord ++ tailWord_330375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330375).length < 2 ^ (prefixWord ++ tailWord_330375).sum := by decide
  have hdescent : baseEnd_330375 < baseStart_330375 := by decide
  rcases family_descends (prefixWord ++ tailWord_330375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330392 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 2, 3, 2]
def baseStart_330392 : Nat := 118140960795 + 330392 * 2 ^ 59
def prefixEnd_330392 : Nat := 4983230072969 + 3 ^ 40 * 330392 * 2
def baseEnd_330392 : Nat := 169649900400376573480561

theorem tailTrace_330392 : CollatzResearch.WordTrace tailWord_330392 prefixEnd_330392 169649900400376573480561 := by
  unfold tailWord_330392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025193109526842653184715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8033590812702456870912953 6025193109526842653184715)
  ·
    refine ⟨9037789664290263979777073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6025193109526842653184715 9037789664290263979777073)
    ·
      refine ⟨6778342248217697984832805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9037789664290263979777073 6778342248217697984832805)
      ·
        refine ⟨1270939171540818372156151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6778342248217697984832805 1270939171540818372156151)
        ·
          refine ⟨1906408757311227558234227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270939171540818372156151 1906408757311227558234227)
          ·
            refine ⟨2859613135966841337351341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906408757311227558234227 2859613135966841337351341)
            ·
              refine ⟨1072354925987565501506753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859613135966841337351341 1072354925987565501506753)
              ·
                refine ⟨804266194490674126130065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072354925987565501506753 804266194490674126130065)
                ·
                  refine ⟨603199645868005594597549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804266194490674126130065 603199645868005594597549)
                  ·
                    refine ⟨226199867200502097974081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603199645868005594597549 226199867200502097974081)
                    ·
                      refine ⟨169649900400376573480561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226199867200502097974081 169649900400376573480561)
                      ·
                        rfl

theorem cell23_330392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_330392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330392 prefixEnd_330392 := by exact prefixLift 330392
  have htrace : WordTrace (prefixWord ++ tailWord_330392) baseStart_330392 baseEnd_330392 := by
    simpa [prefixWord, tailWord_330392, baseEnd_330392] using wordTrace_append hprefix tailTrace_330392
  have hstable : (prefixWord ++ tailWord_330392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330392).length < 2 ^ (prefixWord ++ tailWord_330392).sum := by decide
  have hdescent : baseEnd_330392 < baseStart_330392 := by decide
  rcases family_descends (prefixWord ++ tailWord_330392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330428 : List Nat := [2, 2, 2, 3, 1, 1, 1, 11]
def baseStart_330428 : Nat := 118140960795 + 330428 * 2 ^ 59
def prefixEnd_330428 : Nat := 4983230072969 + 3 ^ 40 * 330428 * 2
def baseEnd_330428 : Nat := 6284014285331053060385

theorem tailTrace_330428 : CollatzResearch.WordTrace tailWord_330428 prefixEnd_330428 6284014285331053060385 := by
  unfold tailWord_330428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025849623461631727339969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8034466164615508969786625 6025849623461631727339969)
  ·
    refine ⟨4519387217596223795504977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6025849623461631727339969 4519387217596223795504977)
    ·
      refine ⟨3389540413197167846628733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519387217596223795504977 3389540413197167846628733)
      ·
        refine ⟨1271077654948937942485775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3389540413197167846628733 1271077654948937942485775)
        ·
          refine ⟨1906616482423406913728663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271077654948937942485775 1906616482423406913728663)
          ·
            refine ⟨2859924723635110370592995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906616482423406913728663 2859924723635110370592995)
            ·
              refine ⟨4289887085452665555889493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859924723635110370592995 4289887085452665555889493)
              ·
                refine ⟨6284014285331053060385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 4289887085452665555889493 6284014285331053060385)
                ·
                  rfl

theorem cell23_330428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 11].length) (baseStart_330428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330428 prefixEnd_330428 := by exact prefixLift 330428
  have htrace : WordTrace (prefixWord ++ tailWord_330428) baseStart_330428 baseEnd_330428 := by
    simpa [prefixWord, tailWord_330428, baseEnd_330428] using wordTrace_append hprefix tailTrace_330428
  have hstable : (prefixWord ++ tailWord_330428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330428).length < 2 ^ (prefixWord ++ tailWord_330428).sum := by decide
  have hdescent : baseEnd_330428 < baseStart_330428 := by decide
  rcases family_descends (prefixWord ++ tailWord_330428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330442 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_330442 : Nat := 118140960795 + 330442 * 2 ^ 59
def prefixEnd_330442 : Nat := 4983230072969 + 3 ^ 40 * 330442 * 2
def baseEnd_330442 : Nat := 169675574433101377855331

theorem tailTrace_330442 : CollatzResearch.WordTrace tailWord_330442 prefixEnd_330442 169675574433101377855331 := by
  unfold tailWord_330442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013052467218135961422395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8034806579248362563793053 3013052467218135961422395)
  ·
    refine ⟨4519578700827203942133593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3013052467218135961422395 4519578700827203942133593)
    ·
      refine ⟨3389684025620402956600195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519578700827203942133593 3389684025620402956600195)
      ·
        refine ⟨5084526038430604434900293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389684025620402956600195 5084526038430604434900293)
        ·
          refine ⟨953348632205738331543805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5084526038430604434900293 953348632205738331543805)
          ·
            refine ⟨357505737077151874328927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 953348632205738331543805 357505737077151874328927)
            ·
              refine ⟨536258605615727811493391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357505737077151874328927 536258605615727811493391)
              ·
                refine ⟨804387908423591717240087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536258605615727811493391 804387908423591717240087)
                ·
                  refine ⟨1206581862635387575860131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804387908423591717240087 1206581862635387575860131)
                  ·
                    refine ⟨1809872793953081363790197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1206581862635387575860131 1809872793953081363790197)
                    ·
                      refine ⟨169675574433101377855331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1809872793953081363790197 169675574433101377855331)
                      ·
                        rfl

theorem cell23_330442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_330442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330442 prefixEnd_330442 := by exact prefixLift 330442
  have htrace : WordTrace (prefixWord ++ tailWord_330442) baseStart_330442 baseEnd_330442 := by
    simpa [prefixWord, tailWord_330442, baseEnd_330442] using wordTrace_append hprefix tailTrace_330442
  have hstable : (prefixWord ++ tailWord_330442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330442).length < 2 ^ (prefixWord ++ tailWord_330442).sum := by decide
  have hdescent : baseEnd_330442 < baseStart_330442 := by decide
  rcases family_descends (prefixWord ++ tailWord_330442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330445 : List Nat := [1, 6, 2, 1, 13]
def baseStart_330445 : Nat := 118140960795 + 330445 * 2 ^ 59
def prefixEnd_330445 : Nat := 4983230072969 + 3 ^ 40 * 330445 * 2
def baseEnd_330445 : Nat := 232753243998717237473

theorem tailTrace_330445 : CollatzResearch.WordTrace tailWord_330445 prefixEnd_330445 232753243998717237473 := by
  unfold tailWord_330445
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052319287861675358048789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8034879525241116905365859 12052319287861675358048789)
  ·
    refine ⟨564952466618516032408537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12052319287861675358048789 564952466618516032408537)
    ·
      refine ⟨423714349963887024306403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 564952466618516032408537 423714349963887024306403)
      ·
        refine ⟨635571524945830536459605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423714349963887024306403 635571524945830536459605)
        ·
          refine ⟨232753243998717237473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 635571524945830536459605 232753243998717237473)
          ·
            rfl

theorem cell23_330445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 13].length) (baseStart_330445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330445 prefixEnd_330445 := by exact prefixLift 330445
  have htrace : WordTrace (prefixWord ++ tailWord_330445) baseStart_330445 baseEnd_330445 := by
    simpa [prefixWord, tailWord_330445, baseEnd_330445] using wordTrace_append hprefix tailTrace_330445
  have hstable : (prefixWord ++ tailWord_330445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330445).length < 2 ^ (prefixWord ++ tailWord_330445).sum := by decide
  have hdescent : baseEnd_330445 < baseStart_330445 := by decide
  rcases family_descends (prefixWord ++ tailWord_330445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330450 : List Nat := [3, 2, 2, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_330450 : Nat := 118140960795 + 330450 * 2 ^ 59
def prefixEnd_330450 : Nat := 4983230072969 + 3 ^ 40 * 330450 * 2
def baseEnd_330450 : Nat := 169679682278337346555295

theorem tailTrace_330450 : CollatzResearch.WordTrace tailWord_330450 prefixEnd_330450 169679682278337346555295 := by
  unfold tailWord_330450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013125413210890302995201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8035001101895707474653869 3013125413210890302995201)
  ·
    refine ⟨2259844059908167727246401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3013125413210890302995201 2259844059908167727246401)
    ·
      refine ⟨1694883044931125795434801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2259844059908167727246401 1694883044931125795434801)
      ·
        refine ⟨1271162283698344346576101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1694883044931125795434801 1271162283698344346576101)
        ·
          refine ⟨238342928193439564983019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1271162283698344346576101 238342928193439564983019)
          ·
            refine ⟨357514392290159347474529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238342928193439564983019 357514392290159347474529)
            ·
              refine ⟨268135794217619510605897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357514392290159347474529 268135794217619510605897)
              ·
                refine ⟨201101845663214632954423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268135794217619510605897 201101845663214632954423)
                ·
                  refine ⟨301652768494821949431635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201101845663214632954423 301652768494821949431635)
                  ·
                    refine ⟨452479152742232924147453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 301652768494821949431635 452479152742232924147453)
                    ·
                      refine ⟨169679682278337346555295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 452479152742232924147453 169679682278337346555295)
                      ·
                        rfl

theorem cell23_330450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_330450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330450 prefixEnd_330450 := by exact prefixLift 330450
  have htrace : WordTrace (prefixWord ++ tailWord_330450) baseStart_330450 baseEnd_330450 := by
    simpa [prefixWord, tailWord_330450, baseEnd_330450] using wordTrace_append hprefix tailTrace_330450
  have hstable : (prefixWord ++ tailWord_330450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330450).length < 2 ^ (prefixWord ++ tailWord_330450).sum := by decide
  have hdescent : baseEnd_330450 < baseStart_330450 := by decide
  rcases family_descends (prefixWord ++ tailWord_330450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330456 : List Nat := [2, 1, 2, 2, 3, 3, 1, 4, 1, 2, 2]
def baseStart_330456 : Nat := 118140960795 + 330456 * 2 ^ 59
def prefixEnd_330456 : Nat := 4983230072969 + 3 ^ 40 * 330456 * 2
def baseEnd_330456 : Nat := 169682763162264323080267

theorem tailTrace_330456 : CollatzResearch.WordTrace tailWord_330456 prefixEnd_330456 169682763162264323080267 := by
  unfold tailWord_330456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026360245410912118349611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8035146993881216157799481 6026360245410912118349611)
  ·
    refine ⟨9039540368116368177524417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6026360245410912118349611 9039540368116368177524417)
    ·
      refine ⟨6779655276087276133143313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9039540368116368177524417 6779655276087276133143313)
      ·
        refine ⟨5084741457065457099857485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6779655276087276133143313 5084741457065457099857485)
        ·
          refine ⟨1906778046399546412446557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5084741457065457099857485 1906778046399546412446557)
          ·
            refine ⟨715041767399829904667459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1906778046399546412446557 715041767399829904667459)
            ·
              refine ⟨1072562651099744857001189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715041767399829904667459 1072562651099744857001189)
              ·
                refine ⟨201105497081202160687723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1072562651099744857001189 201105497081202160687723)
                ·
                  refine ⟨301658245621803241031585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201105497081202160687723 301658245621803241031585)
                  ·
                    refine ⟨226243684216352430773689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301658245621803241031585 226243684216352430773689)
                    ·
                      refine ⟨169682763162264323080267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226243684216352430773689 169682763162264323080267)
                      ·
                        rfl

theorem cell23_330456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_330456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330456 prefixEnd_330456 := by exact prefixLift 330456
  have htrace : WordTrace (prefixWord ++ tailWord_330456) baseStart_330456 baseEnd_330456 := by
    simpa [prefixWord, tailWord_330456, baseEnd_330456] using wordTrace_append hprefix tailTrace_330456
  have hstable : (prefixWord ++ tailWord_330456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330456).length < 2 ^ (prefixWord ++ tailWord_330456).sum := by decide
  have hdescent : baseEnd_330456 < baseStart_330456 := by decide
  rcases family_descends (prefixWord ++ tailWord_330456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330458 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_330458 : Nat := 118140960795 + 330458 * 2 ^ 59
def prefixEnd_330458 : Nat := 4983230072969 + 3 ^ 40 * 330458 * 2
def baseEnd_330458 : Nat := 56561263374524438418419

theorem tailTrace_330458 : CollatzResearch.WordTrace tailWord_330458 prefixEnd_330458 56561263374524438418419 := by
  unfold tailWord_330458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013198359203644644568007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8035195624543052385514685 3013198359203644644568007)
  ·
    refine ⟨4519797538805466966852011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3013198359203644644568007 4519797538805466966852011)
    ·
      refine ⟨6779696308208200450278017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4519797538805466966852011 6779696308208200450278017)
      ·
        refine ⟨5084772231156150337708513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6779696308208200450278017 5084772231156150337708513)
        ·
          refine ⟨3813579173367112753281385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5084772231156150337708513 3813579173367112753281385)
          ·
            refine ⟨2860184380025334564961039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813579173367112753281385 2860184380025334564961039)
            ·
              refine ⟨4290276570038001847441559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860184380025334564961039 4290276570038001847441559)
              ·
                refine ⟨6435414855057002771162339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290276570038001847441559 6435414855057002771162339)
                ·
                  refine ⟨9653122282585504156743509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6435414855057002771162339 9653122282585504156743509)
                  ·
                    refine ⟨56561263374524438418419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9653122282585504156743509 56561263374524438418419)
                    ·
                      rfl

theorem cell23_330458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_330458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330458 prefixEnd_330458 := by exact prefixLift 330458
  have htrace : WordTrace (prefixWord ++ tailWord_330458) baseStart_330458 baseEnd_330458 := by
    simpa [prefixWord, tailWord_330458, baseEnd_330458] using wordTrace_append hprefix tailTrace_330458
  have hstable : (prefixWord ++ tailWord_330458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330458).length < 2 ^ (prefixWord ++ tailWord_330458).sum := by decide
  have hdescent : baseEnd_330458 < baseStart_330458 := by decide
  rcases family_descends (prefixWord ++ tailWord_330458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330488 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 1, 8]
def baseStart_330488 : Nat := 118140960795 + 330488 * 2 ^ 59
def prefixEnd_330488 : Nat := 4983230072969 + 3 ^ 40 * 330488 * 2
def baseEnd_330488 : Nat := 56566398181069399293373

theorem tailTrace_330488 : CollatzResearch.WordTrace tailWord_330488 prefixEnd_330488 56566398181069399293373 := by
  unfold tailWord_330488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026943813352946850932059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8035925084470595801242745 6026943813352946850932059)
  ·
    refine ⟨9040415720029420276398089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6026943813352946850932059 9040415720029420276398089)
    ·
      refine ⟨6780311790022065207298567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9040415720029420276398089 6780311790022065207298567)
      ·
        refine ⟨10170467685033097810947851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6780311790022065207298567 10170467685033097810947851)
        ·
          refine ⟨15255701527549646716421777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10170467685033097810947851 15255701527549646716421777)
          ·
            refine ⟨11441776145662235037316333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15255701527549646716421777 11441776145662235037316333)
            ·
              refine ⟨4290666054623338138993625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11441776145662235037316333 4290666054623338138993625)
              ·
                refine ⟨3217999540967503604245219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4290666054623338138993625 3217999540967503604245219)
                ·
                  refine ⟨4826999311451255406367829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3217999540967503604245219 4826999311451255406367829)
                  ·
                    refine ⟨56566398181069399293373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4826999311451255406367829 56566398181069399293373)
                    ·
                      rfl

theorem cell23_330488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_330488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330488 prefixEnd_330488 := by exact prefixLift 330488
  have htrace : WordTrace (prefixWord ++ tailWord_330488) baseStart_330488 baseEnd_330488 := by
    simpa [prefixWord, tailWord_330488, baseEnd_330488] using wordTrace_append hprefix tailTrace_330488
  have hstable : (prefixWord ++ tailWord_330488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330488).length < 2 ^ (prefixWord ++ tailWord_330488).sum := by decide
  have hdescent : baseEnd_330488 < baseStart_330488 := by decide
  rcases family_descends (prefixWord ++ tailWord_330488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330569 : List Nat := [1, 2, 1, 1, 2, 6, 3, 2, 5]
def baseStart_330569 : Nat := 118140960795 + 330569 * 2 ^ 59
def prefixEnd_330569 : Nat := 4983230072969 + 3 ^ 40 * 330569 * 2
def baseEnd_330569 : Nat := 18860087386246931218583

theorem tailTrace_330569 : CollatzResearch.WordTrace tailWord_330569 prefixEnd_330569 18860087386246931218583 := by
  unfold tailWord_330569
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056841939412444535562761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8037894626274963023708507 12056841939412444535562761)
  ·
    refine ⟨9042631454559333401672071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12056841939412444535562761 9042631454559333401672071)
    ·
      refine ⟨13563947181839000102508107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9042631454559333401672071 13563947181839000102508107)
      ·
        refine ⟨20345920772758500153762161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13563947181839000102508107 20345920772758500153762161)
        ·
          refine ⟨15259440579568875115321621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20345920772758500153762161 15259440579568875115321621)
          ·
            refine ⟨715286277167291021030701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15259440579568875115321621 715286277167291021030701)
            ·
              refine ⟨268232353937734132886513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715286277167291021030701 268232353937734132886513)
              ·
                refine ⟨201174265453300599664885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268232353937734132886513 201174265453300599664885)
                ·
                  refine ⟨18860087386246931218583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201174265453300599664885 18860087386246931218583)
                  ·
                    rfl

theorem cell23_330569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 5].length) (baseStart_330569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330569 prefixEnd_330569 := by exact prefixLift 330569
  have htrace : WordTrace (prefixWord ++ tailWord_330569) baseStart_330569 baseEnd_330569 := by
    simpa [prefixWord, tailWord_330569, baseEnd_330569] using wordTrace_append hprefix tailTrace_330569
  have hstable : (prefixWord ++ tailWord_330569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330569).length < 2 ^ (prefixWord ++ tailWord_330569).sum := by decide
  have hdescent : baseEnd_330569 < baseStart_330569 := by decide
  rcases family_descends (prefixWord ++ tailWord_330569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330580 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_330580 : Nat := 118140960795 + 330580 * 2 ^ 59
def prefixEnd_330580 : Nat := 4983230072969 + 3 ^ 40 * 330580 * 2
def baseEnd_330580 : Nat := 169746434763421837929697

theorem tailTrace_330580 : CollatzResearch.WordTrace tailWord_330580 prefixEnd_330580 169746434763421837929697 := by
  unfold tailWord_330580
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028621571186296707106597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8038162094915062276142129 6028621571186296707106597)
  ·
    refine ⟨1130366544597430632582487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6028621571186296707106597 1130366544597430632582487)
    ·
      refine ⟨1695549816896145948873731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130366544597430632582487 1695549816896145948873731)
      ·
        refine ⟨2543324725344218923310597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695549816896145948873731 2543324725344218923310597)
        ·
          refine ⟨476873386002041048120737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2543324725344218923310597 476873386002041048120737)
          ·
            refine ⟨357655039501530786090553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476873386002041048120737 357655039501530786090553)
            ·
              refine ⟨268241279626148089567915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357655039501530786090553 268241279626148089567915)
              ·
                refine ⟨402361919439222134351873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268241279626148089567915 402361919439222134351873)
                ·
                  refine ⟨301771439579416600763905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402361919439222134351873 301771439579416600763905)
                  ·
                    refine ⟨226328579684562450572929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301771439579416600763905 226328579684562450572929)
                    ·
                      refine ⟨169746434763421837929697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226328579684562450572929 169746434763421837929697)
                      ·
                        rfl

theorem cell23_330580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_330580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330580 prefixEnd_330580 := by exact prefixLift 330580
  have htrace : WordTrace (prefixWord ++ tailWord_330580) baseStart_330580 baseEnd_330580 := by
    simpa [prefixWord, tailWord_330580, baseEnd_330580] using wordTrace_append hprefix tailTrace_330580
  have hstable : (prefixWord ++ tailWord_330580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330580).length < 2 ^ (prefixWord ++ tailWord_330580).sum := by decide
  have hdescent : baseEnd_330580 < baseStart_330580 := by decide
  rcases family_descends (prefixWord ++ tailWord_330580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330663 : List Nat := [1, 1, 6, 1, 3, 1, 2, 3, 1, 4]
def baseStart_330663 : Nat := 118140960795 + 330663 * 2 ^ 59
def prefixEnd_330663 : Nat := 4983230072969 + 3 ^ 40 * 330663 * 2
def baseEnd_330663 : Nat := 56596351219248337730605

theorem tailTrace_330663 : CollatzResearch.WordTrace tailWord_330663 prefixEnd_330663 56596351219248337730605 := by
  unfold tailWord_330663
  simp only [CollatzResearch.WordTrace]
  refine ⟨12060270401071898589484643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8040180267381265726323095 12060270401071898589484643)
  ·
    refine ⟨18090405601607847884226965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12060270401071898589484643 18090405601607847884226965)
    ·
      refine ⟨847987762575367869573139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18090405601607847884226965 847987762575367869573139)
      ·
        refine ⟨1271981643863051804359709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847987762575367869573139 1271981643863051804359709)
        ·
          refine ⟨476993116448644426634891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1271981643863051804359709 476993116448644426634891)
          ·
            refine ⟨715489674672966639952337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476993116448644426634891 715489674672966639952337)
            ·
              refine ⟨536617256004724979964253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715489674672966639952337 536617256004724979964253)
              ·
                refine ⟨201231471001771867486595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536617256004724979964253 201231471001771867486595)
                ·
                  refine ⟨301847206502657801229893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201231471001771867486595 301847206502657801229893)
                  ·
                    refine ⟨56596351219248337730605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301847206502657801229893 56596351219248337730605)
                    ·
                      rfl

theorem cell23_330663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_330663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330663 prefixEnd_330663 := by exact prefixLift 330663
  have htrace : WordTrace (prefixWord ++ tailWord_330663) baseStart_330663 baseEnd_330663 := by
    simpa [prefixWord, tailWord_330663, baseEnd_330663] using wordTrace_append hprefix tailTrace_330663
  have hstable : (prefixWord ++ tailWord_330663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330663).length < 2 ^ (prefixWord ++ tailWord_330663).sum := by decide
  have hdescent : baseEnd_330663 < baseStart_330663 := by decide
  rcases family_descends (prefixWord ++ tailWord_330663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330676 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 6]
def baseStart_330676 : Nat := 118140960795 + 330676 * 2 ^ 59
def prefixEnd_330676 : Nat := 4983230072969 + 3 ^ 40 * 330676 * 2
def baseEnd_330676 : Nat := 18866192100694829147695

theorem tailTrace_330676 : CollatzResearch.WordTrace tailWord_330676 prefixEnd_330676 18866192100694829147695 := by
  unfold tailWord_330676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030372275012400904853941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8040496366683201206471921 6030372275012400904853941)
  ·
    refine ⟨565347400782412584830057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6030372275012400904853941 565347400782412584830057)
    ·
      refine ⟨424010550586809438622543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 565347400782412584830057 424010550586809438622543)
      ·
        refine ⟨636015825880214157933815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424010550586809438622543 636015825880214157933815)
        ·
          refine ⟨954023738820321236900723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636015825880214157933815 954023738820321236900723)
          ·
            refine ⟨1431035608230481855351085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954023738820321236900723 1431035608230481855351085)
            ·
              refine ⟨536638353086430695756657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1431035608230481855351085 536638353086430695756657)
              ·
                refine ⟨402478764814823021817493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536638353086430695756657 402478764814823021817493)
                ·
                  refine ⟨18866192100694829147695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 402478764814823021817493 18866192100694829147695)
                  ·
                    rfl

theorem cell23_330676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_330676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330676 prefixEnd_330676 := by exact prefixLift 330676
  have htrace : WordTrace (prefixWord ++ tailWord_330676) baseStart_330676 baseEnd_330676 := by
    simpa [prefixWord, tailWord_330676, baseEnd_330676] using wordTrace_append hprefix tailTrace_330676
  have hstable : (prefixWord ++ tailWord_330676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330676).length < 2 ^ (prefixWord ++ tailWord_330676).sum := by decide
  have hdescent : baseEnd_330676 < baseStart_330676 := by decide
  rcases family_descends (prefixWord ++ tailWord_330676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330679 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 2, 3, 2]
def baseStart_330679 : Nat := 118140960795 + 330679 * 2 ^ 59
def prefixEnd_330679 : Nat := 4983230072969 + 3 ^ 40 * 330679 * 2
def baseEnd_330679 : Nat := 169797269348216950591741

theorem tailTrace_330679 : CollatzResearch.WordTrace tailWord_330679 prefixEnd_330679 169797269348216950591741 := by
  unfold tailWord_330679
  simp only [CollatzResearch.WordTrace]
  refine ⟨12060853969013933322067091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8040569312675955548044727 12060853969013933322067091)
  ·
    refine ⟨18091280953520899983100637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12060853969013933322067091 18091280953520899983100637)
    ·
      refine ⟨6784230357570337493662739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18091280953520899983100637 6784230357570337493662739)
      ·
        refine ⟨10176345536355506240494109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6784230357570337493662739 10176345536355506240494109)
        ·
          refine ⟨3816129576133314840185291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10176345536355506240494109 3816129576133314840185291)
          ·
            refine ⟨5724194364199972260277937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816129576133314840185291 5724194364199972260277937)
            ·
              refine ⟨4293145773149979195208453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5724194364199972260277937 4293145773149979195208453)
              ·
                refine ⟨804964832465621099101585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4293145773149979195208453 804964832465621099101585)
                ·
                  refine ⟨603723624349215824326189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804964832465621099101585 603723624349215824326189)
                  ·
                    refine ⟨226396359130955934122321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603723624349215824326189 226396359130955934122321)
                    ·
                      refine ⟨169797269348216950591741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226396359130955934122321 169797269348216950591741)
                      ·
                        rfl

theorem cell23_330679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_330679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330679 prefixEnd_330679 := by exact prefixLift 330679
  have htrace : WordTrace (prefixWord ++ tailWord_330679) baseStart_330679 baseEnd_330679 := by
    simpa [prefixWord, tailWord_330679, baseEnd_330679] using wordTrace_append hprefix tailTrace_330679
  have hstable : (prefixWord ++ tailWord_330679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330679).length < 2 ^ (prefixWord ++ tailWord_330679).sum := by decide
  have hdescent : baseEnd_330679 < baseStart_330679 := by decide
  rcases family_descends (prefixWord ++ tailWord_330679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330686 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_330686 : Nat := 118140960795 + 330686 * 2 ^ 59
def prefixEnd_330686 : Nat := 4983230072969 + 3 ^ 40 * 330686 * 2
def baseEnd_330686 : Nat := 169800863712798423204209

theorem tailTrace_330686 : CollatzResearch.WordTrace tailWord_330686 prefixEnd_330686 169800863712798423204209 := by
  unfold tailWord_330686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507638659998571689696489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8040739519992382345047941 1507638659998571689696489)
  ·
    refine ⟨1130728994998928767272367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1507638659998571689696489 1130728994998928767272367)
    ·
      refine ⟨1696093492498393150908551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130728994998928767272367 1696093492498393150908551)
      ·
        refine ⟨2544140238747589726362827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696093492498393150908551 2544140238747589726362827)
        ·
          refine ⟨3816210358121384589544241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544140238747589726362827 3816210358121384589544241)
          ·
            refine ⟨2862157768591038442158181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3816210358121384589544241 2862157768591038442158181)
            ·
              refine ⟨536654581610819707904659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2862157768591038442158181 536654581610819707904659)
              ·
                refine ⟨804981872416229561856989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536654581610819707904659 804981872416229561856989)
                ·
                  refine ⟨301868202156086085696371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804981872416229561856989 301868202156086085696371)
                  ·
                    refine ⟨452802303234129128544557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 301868202156086085696371 452802303234129128544557)
                    ·
                      refine ⟨169800863712798423204209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 452802303234129128544557 169800863712798423204209)
                      ·
                        rfl

theorem cell23_330686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_330686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330686 prefixEnd_330686 := by exact prefixLift 330686
  have htrace : WordTrace (prefixWord ++ tailWord_330686) baseStart_330686 baseEnd_330686 := by
    simpa [prefixWord, tailWord_330686, baseEnd_330686] using wordTrace_append hprefix tailTrace_330686
  have hstable : (prefixWord ++ tailWord_330686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330686).length < 2 ^ (prefixWord ++ tailWord_330686).sum := by decide
  have hdescent : baseEnd_330686 < baseStart_330686 := by decide
  rcases family_descends (prefixWord ++ tailWord_330686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330706 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_330706 : Nat := 118140960795 + 330706 * 2 ^ 59
def prefixEnd_330706 : Nat := 4983230072969 + 3 ^ 40 * 330706 * 2
def baseEnd_330706 : Nat := 56603711108629448318039

theorem tailTrace_330706 : CollatzResearch.WordTrace tailWord_330706 prefixEnd_330706 56603711108629448318039 := by
  unfold tailWord_330706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015459684979029233324993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8041225826610744622199981 3015459684979029233324993)
  ·
    refine ⟨2261594763734271924993745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3015459684979029233324993 2261594763734271924993745)
    ·
      refine ⟨1696196072800703943745309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2261594763734271924993745 1696196072800703943745309)
      ·
        refine ⟨636073527300263978904491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1696196072800703943745309 636073527300263978904491)
        ·
          refine ⟨954110290950395968356737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636073527300263978904491 954110290950395968356737)
          ·
            refine ⟨715582718212796976267553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954110290950395968356737 715582718212796976267553)
            ·
              refine ⟨536687038659597732200665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715582718212796976267553 536687038659597732200665)
              ·
                refine ⟨402515278994698299150499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536687038659597732200665 402515278994698299150499)
                ·
                  refine ⟨603772918492047448725749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402515278994698299150499 603772918492047448725749)
                  ·
                    refine ⟨56603711108629448318039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 603772918492047448725749 56603711108629448318039)
                    ·
                      rfl

theorem cell23_330706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_330706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330706 prefixEnd_330706 := by exact prefixLift 330706
  have htrace : WordTrace (prefixWord ++ tailWord_330706) baseStart_330706 baseEnd_330706 := by
    simpa [prefixWord, tailWord_330706, baseEnd_330706] using wordTrace_append hprefix tailTrace_330706
  have hstable : (prefixWord ++ tailWord_330706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330706).length < 2 ^ (prefixWord ++ tailWord_330706).sum := by decide
  have hdescent : baseEnd_330706 < baseStart_330706 := by decide
  rcases family_descends (prefixWord ++ tailWord_330706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330753 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 2, 4]
def baseStart_330753 : Nat := 118140960795 + 330753 * 2 ^ 59
def prefixEnd_330753 : Nat := 4983230072969 + 3 ^ 40 * 330753 * 2
def baseEnd_330753 : Nat := 56611755638883220355467

theorem tailTrace_330753 : CollatzResearch.WordTrace tailWord_330753 prefixEnd_330753 56611755638883220355467 := by
  unfold tailWord_330753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12063552970745843960260913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8042368647163895973507275 12063552970745843960260913)
  ·
    refine ⟨9047664728059382970195685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12063552970745843960260913 9047664728059382970195685)
    ·
      refine ⟨1696437136511134306911691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9047664728059382970195685 1696437136511134306911691)
      ·
        refine ⟨2544655704766701460367537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696437136511134306911691 2544655704766701460367537)
        ·
          refine ⟨1908491778575026095275653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2544655704766701460367537 1908491778575026095275653)
          ·
            refine ⟨357842208482817392864185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1908491778575026095275653 357842208482817392864185)
            ·
              refine ⟨268381656362113044648139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357842208482817392864185 268381656362113044648139)
              ·
                refine ⟨402572484543169566972209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268381656362113044648139 402572484543169566972209)
                ·
                  refine ⟨301929363407377175229157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402572484543169566972209 301929363407377175229157)
                  ·
                    refine ⟨56611755638883220355467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 301929363407377175229157 56611755638883220355467)
                    ·
                      rfl

theorem cell23_330753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_330753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330753 prefixEnd_330753 := by exact prefixLift 330753
  have htrace : WordTrace (prefixWord ++ tailWord_330753) baseStart_330753 baseEnd_330753 := by
    simpa [prefixWord, tailWord_330753, baseEnd_330753] using wordTrace_append hprefix tailTrace_330753
  have hstable : (prefixWord ++ tailWord_330753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330753).length < 2 ^ (prefixWord ++ tailWord_330753).sum := by decide
  have hdescent : baseEnd_330753 < baseStart_330753 := by decide
  rcases family_descends (prefixWord ++ tailWord_330753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330759 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_330759 : Nat := 118140960795 + 330759 * 2 ^ 59
def prefixEnd_330759 : Nat := 4983230072969 + 3 ^ 40 * 330759 * 2
def baseEnd_330759 : Nat := 169838347800576637591373

theorem tailTrace_330759 : CollatzResearch.WordTrace tailWord_330759 prefixEnd_330759 169838347800576637591373 := by
  unfold tailWord_330759
  simp only [CollatzResearch.WordTrace]
  refine ⟨12063771808724106984979331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8042514539149404656652887 12063771808724106984979331)
  ·
    refine ⟨18095657713086160477468997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12063771808724106984979331 18095657713086160477468997)
    ·
      refine ⟨3392935821203655089525437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18095657713086160477468997 3392935821203655089525437)
      ·
        refine ⟨1272350932951370658572039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3392935821203655089525437 1272350932951370658572039)
        ·
          refine ⟨1908526399427055987858059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272350932951370658572039 1908526399427055987858059)
          ·
            refine ⟨2862789599140583981787089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908526399427055987858059 2862789599140583981787089)
            ·
              refine ⟨2147092199355437986340317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2862789599140583981787089 2147092199355437986340317)
              ·
                refine ⟨805159574758289244877619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2147092199355437986340317 805159574758289244877619)
                ·
                  refine ⟨1207739362137433867316429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805159574758289244877619 1207739362137433867316429)
                  ·
                    refine ⟨452902260801537700243661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1207739362137433867316429 452902260801537700243661)
                    ·
                      refine ⟨169838347800576637591373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 452902260801537700243661 169838347800576637591373)
                      ·
                        rfl

theorem cell23_330759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_330759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330759 prefixEnd_330759 := by exact prefixLift 330759
  have htrace : WordTrace (prefixWord ++ tailWord_330759) baseStart_330759 baseEnd_330759 := by
    simpa [prefixWord, tailWord_330759, baseEnd_330759] using wordTrace_append hprefix tailTrace_330759
  have hstable : (prefixWord ++ tailWord_330759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330759).length < 2 ^ (prefixWord ++ tailWord_330759).sum := by decide
  have hdescent : baseEnd_330759 < baseStart_330759 := by decide
  rcases family_descends (prefixWord ++ tailWord_330759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_330794 : List Nat := [3, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_330794 : Nat := 118140960795 + 330794 * 2 ^ 59
def prefixEnd_330794 : Nat := 4983230072969 + 3 ^ 40 * 330794 * 2
def baseEnd_330794 : Nat := 169856319623484000653713

theorem tailTrace_330794 : CollatzResearch.WordTrace tailWord_330794 prefixEnd_330794 169856319623484000653713 := by
  unfold tailWord_330794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016262090899326990625859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8043365575731538641668957 3016262090899326990625859)
  ·
    refine ⟨4524393136348990485938789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3016262090899326990625859 4524393136348990485938789)
    ·
      refine ⟨848323713065435716113523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4524393136348990485938789 848323713065435716113523)
      ·
        refine ⟨1272485569598153574170285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848323713065435716113523 1272485569598153574170285)
        ·
          refine ⟨477182088599307590313857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1272485569598153574170285 477182088599307590313857)
          ·
            refine ⟨357886566449480692735393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477182088599307590313857 357886566449480692735393)
            ·
              refine ⟨268414924837110519551545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357886566449480692735393 268414924837110519551545)
              ·
                refine ⟨201311193627832889663659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268414924837110519551545 201311193627832889663659)
                ·
                  refine ⟨301966790441749334495489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 201311193627832889663659 301966790441749334495489)
                  ·
                    refine ⟨226475092831312000871617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 301966790441749334495489 226475092831312000871617)
                    ·
                      refine ⟨169856319623484000653713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 226475092831312000871617 169856319623484000653713)
                      ·
                        rfl

theorem cell23_330794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_330794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_330794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_330794 prefixEnd_330794 := by exact prefixLift 330794
  have htrace : WordTrace (prefixWord ++ tailWord_330794) baseStart_330794 baseEnd_330794 := by
    simpa [prefixWord, tailWord_330794, baseEnd_330794] using wordTrace_append hprefix tailTrace_330794
  have hstable : (prefixWord ++ tailWord_330794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_330794).length < 2 ^ (prefixWord ++ tailWord_330794).sum := by decide
  have hdescent : baseEnd_330794 < baseStart_330794 := by decide
  rcases family_descends (prefixWord ++ tailWord_330794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
