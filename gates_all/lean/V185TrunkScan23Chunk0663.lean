import V185TrunkScan23Chunk0662

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3919761 : List Nat := [1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_3919761 : Nat := 118140960795 + 3919761 * 2 ^ 59
def prefixEnd_3919761 : Nat := 4983230072969 + 3 ^ 40 * 3919761 * 2
def baseEnd_3919761 : Nat := 2012721443748343650760853

theorem tailTrace_3919761 : CollatzResearch.WordTrace tailWord_3919761 prefixEnd_3919761 2012721443748343650760853 := by
  unfold tailWord_3919761
  simp only [CollatzResearch.WordTrace]
  refine ⟨142965428752382813726919137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95310285834921875817946091 142965428752382813726919137)
  ·
    refine ⟨107224071564287110295189353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142965428752382813726919137 107224071564287110295189353)
    ·
      refine ⟨80418053673215332721392015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107224071564287110295189353 80418053673215332721392015)
      ·
        refine ⟨120627080509822999082088023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80418053673215332721392015 120627080509822999082088023)
        ·
          refine ⟨180940620764734498623132035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120627080509822999082088023 180940620764734498623132035)
          ·
            refine ⟨271410931147101747934698053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180940620764734498623132035 271410931147101747934698053)
            ·
              refine ⟨50889549590081577737755885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271410931147101747934698053 50889549590081577737755885)
              ·
                refine ⟨19083581096280591651658457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50889549590081577737755885 19083581096280591651658457)
                ·
                  refine ⟨14312685822210443738743843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19083581096280591651658457 14312685822210443738743843)
                  ·
                    refine ⟨21469028733315665608115765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14312685822210443738743843 21469028733315665608115765)
                    ·
                      refine ⟨2012721443748343650760853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21469028733315665608115765 2012721443748343650760853)
                      ·
                        rfl

theorem cell23_3919761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_3919761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919761 prefixEnd_3919761 := by exact prefixLift 3919761
  have htrace : WordTrace (prefixWord ++ tailWord_3919761) baseStart_3919761 baseEnd_3919761 := by
    simpa [prefixWord, tailWord_3919761, baseEnd_3919761] using wordTrace_append hprefix tailTrace_3919761
  have hstable : (prefixWord ++ tailWord_3919761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919761).length < 2 ^ (prefixWord ++ tailWord_3919761).sum := by decide
  have hdescent : baseEnd_3919761 < baseStart_3919761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919796 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_3919796 : Nat := 118140960795 + 3919796 * 2 ^ 59
def prefixEnd_3919796 : Nat := 4983230072969 + 3 ^ 40 * 3919796 * 2
def baseEnd_3919796 : Nat := 2012739415571251013823193

theorem tailTrace_3919796 : CollatzResearch.WordTrace tailWord_3919796 prefixEnd_3919796 2012739415571251013823193 := by
  unfold tailWord_3919796
  simp only [CollatzResearch.WordTrace]
  refine ⟨71483352653628007352221621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95311136871504009802962161 71483352653628007352221621)
  ·
    refine ⟨6701564311277625689270777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71483352653628007352221621 6701564311277625689270777)
    ·
      refine ⟨5026173233458219266953083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6701564311277625689270777 5026173233458219266953083)
      ·
        refine ⟨7539259850187328900429625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5026173233458219266953083 7539259850187328900429625)
        ·
          refine ⟨5654444887640496675322219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7539259850187328900429625 5654444887640496675322219)
          ·
            refine ⟨8481667331460745012983329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5654444887640496675322219 8481667331460745012983329)
            ·
              refine ⟨6361250498595558759737497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8481667331460745012983329 6361250498595558759737497)
              ·
                refine ⟨4770937873946669069803123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6361250498595558759737497 4770937873946669069803123)
                ·
                  refine ⟨7156406810920003604704685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770937873946669069803123 7156406810920003604704685)
                  ·
                    refine ⟨2683652554095001351764257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7156406810920003604704685 2683652554095001351764257)
                    ·
                      refine ⟨2012739415571251013823193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683652554095001351764257 2012739415571251013823193)
                      ·
                        rfl

theorem cell23_3919796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_3919796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919796 prefixEnd_3919796 := by exact prefixLift 3919796
  have htrace : WordTrace (prefixWord ++ tailWord_3919796) baseStart_3919796 baseEnd_3919796 := by
    simpa [prefixWord, tailWord_3919796, baseEnd_3919796] using wordTrace_append hprefix tailTrace_3919796
  have hstable : (prefixWord ++ tailWord_3919796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919796).length < 2 ^ (prefixWord ++ tailWord_3919796).sum := by decide
  have hdescent : baseEnd_3919796 < baseStart_3919796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919848 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3919848 : Nat := 118140960795 + 3919848 * 2 ^ 59
def prefixEnd_3919848 : Nat := 4983230072969 + 3 ^ 40 * 3919848 * 2
def baseEnd_3919848 : Nat := 2012766116565284810372953

theorem tailTrace_3919848 : CollatzResearch.WordTrace tailWord_3919848 prefixEnd_3919848 2012766116565284810372953 := by
  unfold tailWord_3919848
  simp only [CollatzResearch.WordTrace]
  refine ⟨71484300951533813792668099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95312401268711751723557465 71484300951533813792668099)
  ·
    refine ⟨107226451427300720689002149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71484300951533813792668099 107226451427300720689002149)
    ·
      refine ⟨20104959642618885129187903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107226451427300720689002149 20104959642618885129187903)
      ·
        refine ⟨30157439463928327693781855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20104959642618885129187903 30157439463928327693781855)
        ·
          refine ⟨45236159195892491540672783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30157439463928327693781855 45236159195892491540672783)
          ·
            refine ⟨67854238793838737311009175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45236159195892491540672783 67854238793838737311009175)
            ·
              refine ⟨101781358190758105966513763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67854238793838737311009175 101781358190758105966513763)
              ·
                refine ⟨152672037286137158949770645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101781358190758105966513763 152672037286137158949770645)
                ·
                  refine ⟨7156501747787679325770499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152672037286137158949770645 7156501747787679325770499)
                  ·
                    refine ⟨10734752621681518988655749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7156501747787679325770499 10734752621681518988655749)
                    ·
                      refine ⟨2012766116565284810372953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10734752621681518988655749 2012766116565284810372953)
                      ·
                        rfl

theorem cell23_3919848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3919848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919848 prefixEnd_3919848 := by exact prefixLift 3919848
  have htrace : WordTrace (prefixWord ++ tailWord_3919848) baseStart_3919848 baseEnd_3919848 := by
    simpa [prefixWord, tailWord_3919848, baseEnd_3919848] using wordTrace_append hprefix tailTrace_3919848
  have hstable : (prefixWord ++ tailWord_3919848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919848).length < 2 ^ (prefixWord ++ tailWord_3919848).sum := by decide
  have hdescent : baseEnd_3919848 < baseStart_3919848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919851 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5]
def baseStart_3919851 : Nat := 118140960795 + 3919851 * 2 ^ 59
def prefixEnd_3919851 : Nat := 4983230072969 + 3 ^ 40 * 3919851 * 2
def baseEnd_3919851 : Nat := 2012767657007248298635439

theorem tailTrace_3919851 : CollatzResearch.WordTrace tailWord_3919851 prefixEnd_3919851 2012767657007248298635439 := by
  unfold tailWord_3919851
  simp only [CollatzResearch.WordTrace]
  refine ⟨142968711322056759097695407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95312474214704506065130271 142968711322056759097695407)
  ·
    refine ⟨214453066983085138646543111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142968711322056759097695407 214453066983085138646543111)
    ·
      refine ⟨321679600474627707969814667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214453066983085138646543111 321679600474627707969814667)
      ·
        refine ⟨482519400711941561954722001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321679600474627707969814667 482519400711941561954722001)
        ·
          refine ⟨361889550533956171466041501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482519400711941561954722001 361889550533956171466041501)
          ·
            refine ⟨135708581450233564299765563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361889550533956171466041501 135708581450233564299765563)
            ·
              refine ⟨203562872175350346449648345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135708581450233564299765563 203562872175350346449648345)
              ·
                refine ⟨152672154131512759837236259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203562872175350346449648345 152672154131512759837236259)
                ·
                  refine ⟨229008231197269139755854389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152672154131512759837236259 229008231197269139755854389)
                  ·
                    refine ⟨21469521674743981852111349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229008231197269139755854389 21469521674743981852111349)
                    ·
                      refine ⟨2012767657007248298635439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21469521674743981852111349 2012767657007248298635439)
                      ·
                        rfl

theorem cell23_3919851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_3919851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919851 prefixEnd_3919851 := by exact prefixLift 3919851
  have htrace : WordTrace (prefixWord ++ tailWord_3919851) baseStart_3919851 baseEnd_3919851 := by
    simpa [prefixWord, tailWord_3919851, baseEnd_3919851] using wordTrace_append hprefix tailTrace_3919851
  have hstable : (prefixWord ++ tailWord_3919851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919851).length < 2 ^ (prefixWord ++ tailWord_3919851).sum := by decide
  have hdescent : baseEnd_3919851 < baseStart_3919851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919862 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_3919862 : Nat := 118140960795 + 3919862 * 2 ^ 59
def prefixEnd_3919862 : Nat := 4983230072969 + 3 ^ 40 * 3919862 * 2
def baseEnd_3919862 : Nat := 670924435098149251865963

theorem tailTrace_3919862 : CollatzResearch.WordTrace tailWord_3919862 prefixEnd_3919862 670924435098149251865963 := by
  unfold tailWord_3919862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935569532813556748521615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95312741683344605317563893 8935569532813556748521615)
  ·
    refine ⟨13403354299220335122782423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8935569532813556748521615 13403354299220335122782423)
    ·
      refine ⟨20105031448830502684173635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13403354299220335122782423 20105031448830502684173635)
      ·
        refine ⟨30157547173245754026260453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20105031448830502684173635 30157547173245754026260453)
        ·
          refine ⟨5654540094983578879923835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30157547173245754026260453 5654540094983578879923835)
          ·
            refine ⟨8481810142475368319885753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5654540094983578879923835 8481810142475368319885753)
            ·
              refine ⟨6361357606856526239914315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8481810142475368319885753 6361357606856526239914315)
              ·
                refine ⟨9542036410284789359871473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361357606856526239914315 9542036410284789359871473)
                ·
                  refine ⟨7156527307713592019903605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9542036410284789359871473 7156527307713592019903605)
                  ·
                    refine ⟨670924435098149251865963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7156527307713592019903605 670924435098149251865963)
                    ·
                      rfl

theorem cell23_3919862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_3919862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919862 prefixEnd_3919862 := by exact prefixLift 3919862
  have htrace : WordTrace (prefixWord ++ tailWord_3919862) baseStart_3919862 baseEnd_3919862 := by
    simpa [prefixWord, tailWord_3919862, baseEnd_3919862] using wordTrace_append hprefix tailTrace_3919862
  have hstable : (prefixWord ++ tailWord_3919862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919862).length < 2 ^ (prefixWord ++ tailWord_3919862).sum := by decide
  have hdescent : baseEnd_3919862 < baseStart_3919862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919865 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 4]
def baseStart_3919865 : Nat := 118140960795 + 3919865 * 2 ^ 59
def prefixEnd_3919865 : Nat := 4983230072969 + 3 ^ 40 * 3919865 * 2
def baseEnd_3919865 : Nat := 2012774845736411243860375

theorem tailTrace_3919865 : CollatzResearch.WordTrace tailWord_3919865 prefixEnd_3919865 2012774845736411243860375 := by
  unfold tailWord_3919865
  simp only [CollatzResearch.WordTrace]
  refine ⟨142969221944006039488705049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95312814629337359659136699 142969221944006039488705049)
  ·
    refine ⟨107226916458004529616528787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142969221944006039488705049 107226916458004529616528787)
    ·
      refine ⟨160840374687006794424793181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107226916458004529616528787 160840374687006794424793181)
      ·
        refine ⟨60315140507627547909297443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160840374687006794424793181 60315140507627547909297443)
        ·
          refine ⟨90472710761441321863946165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60315140507627547909297443 90472710761441321863946165)
          ·
            refine ⟨8481816633885123924744953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90472710761441321863946165 8481816633885123924744953)
            ·
              refine ⟨6361362475413842943558715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8481816633885123924744953 6361362475413842943558715)
              ·
                refine ⟨9542043713120764415338073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361362475413842943558715 9542043713120764415338073)
                ·
                  refine ⟨7156532784840573311503555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9542043713120764415338073 7156532784840573311503555)
                  ·
                    refine ⟨10734799177260859967255333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7156532784840573311503555 10734799177260859967255333)
                    ·
                      refine ⟨2012774845736411243860375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10734799177260859967255333 2012774845736411243860375)
                      ·
                        rfl

theorem cell23_3919865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_3919865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919865 prefixEnd_3919865 := by exact prefixLift 3919865
  have htrace : WordTrace (prefixWord ++ tailWord_3919865) baseStart_3919865 baseEnd_3919865 := by
    simpa [prefixWord, tailWord_3919865, baseEnd_3919865] using wordTrace_append hprefix tailTrace_3919865
  have hstable : (prefixWord ++ tailWord_3919865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919865).length < 2 ^ (prefixWord ++ tailWord_3919865).sum := by decide
  have hdescent : baseEnd_3919865 < baseStart_3919865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919871 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 10]
def baseStart_3919871 : Nat := 118140960795 + 3919871 * 2 ^ 59
def prefixEnd_3919871 : Nat := 4983230072969 + 3 ^ 40 * 3919871 * 2
def baseEnd_3919871 : Nat := 223641991846704246709483

theorem tailTrace_3919871 : CollatzResearch.WordTrace tailWord_3919871 prefixEnd_3919871 223641991846704246709483 := by
  unfold tailWord_3919871
  simp only [CollatzResearch.WordTrace]
  refine ⟨142969440781984302513423467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95312960521322868342282311 142969440781984302513423467)
  ·
    refine ⟨214454161172976453770135201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142969440781984302513423467 214454161172976453770135201)
    ·
      refine ⟨160840620879732340327601401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214454161172976453770135201 160840620879732340327601401)
      ·
        refine ⟨120630465659799255245701051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160840620879732340327601401 120630465659799255245701051)
        ·
          refine ⟨180945698489698882868551577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120630465659799255245701051 180945698489698882868551577)
          ·
            refine ⟨135709273867274162151413683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180945698489698882868551577 135709273867274162151413683)
            ·
              refine ⟨203563910800911243227120525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135709273867274162151413683 203563910800911243227120525)
              ·
                refine ⟨76336466550341716210170197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203563910800911243227120525 76336466550341716210170197)
                ·
                  refine ⟨223641991846704246709483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 76336466550341716210170197 223641991846704246709483)
                  ·
                    rfl

theorem cell23_3919871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 10].length) (baseStart_3919871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919871 prefixEnd_3919871 := by exact prefixLift 3919871
  have htrace : WordTrace (prefixWord ++ tailWord_3919871) baseStart_3919871 baseEnd_3919871 := by
    simpa [prefixWord, tailWord_3919871, baseEnd_3919871] using wordTrace_append hprefix tailTrace_3919871
  have hstable : (prefixWord ++ tailWord_3919871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919871).length < 2 ^ (prefixWord ++ tailWord_3919871).sum := by decide
  have hdescent : baseEnd_3919871 < baseStart_3919871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919948 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_3919948 : Nat := 118140960795 + 3919948 * 2 ^ 59
def prefixEnd_3919948 : Nat := 4983230072969 + 3 ^ 40 * 3919948 * 2
def baseEnd_3919948 : Nat := 670939154876911473040831

theorem tailTrace_3919948 : CollatzResearch.WordTrace tailWord_3919948 prefixEnd_3919948 670939154876911473040831 := by
  unfold tailWord_3919948
  simp only [CollatzResearch.WordTrace]
  refine ⟨71486124601352672331988249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95314832801803563109317665 71486124601352672331988249)
  ·
    refine ⟨53614593451014504248991187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71486124601352672331988249 53614593451014504248991187)
    ·
      refine ⟨80421890176521756373486781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53614593451014504248991187 80421890176521756373486781)
      ·
        refine ⟨30158208816195658640057543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80421890176521756373486781 30158208816195658640057543)
        ·
          refine ⟨45237313224293487960086315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30158208816195658640057543 45237313224293487960086315)
          ·
            refine ⟨67855969836440231940129473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45237313224293487960086315 67855969836440231940129473)
            ·
              refine ⟨50891977377330173955097105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67855969836440231940129473 50891977377330173955097105)
              ·
                refine ⟨38168983032997630466322829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50891977377330173955097105 38168983032997630466322829)
                ·
                  refine ⟨14313368637374111424871061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38168983032997630466322829 14313368637374111424871061)
                  ·
                    refine ⟨670939154876911473040831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14313368637374111424871061 670939154876911473040831)
                    ·
                      rfl

theorem cell23_3919948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_3919948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919948 prefixEnd_3919948 := by exact prefixLift 3919948
  have htrace : WordTrace (prefixWord ++ tailWord_3919948) baseStart_3919948 baseEnd_3919948 := by
    simpa [prefixWord, tailWord_3919948, baseEnd_3919948] using wordTrace_append hprefix tailTrace_3919948
  have hstable : (prefixWord ++ tailWord_3919948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919948).length < 2 ^ (prefixWord ++ tailWord_3919948).sum := by decide
  have hdescent : baseEnd_3919948 < baseStart_3919948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3919949 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3919949 : Nat := 118140960795 + 3919949 * 2 ^ 59
def prefixEnd_3919949 : Nat := 4983230072969 + 3 ^ 40 * 3919949 * 2
def baseEnd_3919949 : Nat := 2012817978111388915209989

theorem tailTrace_3919949 : CollatzResearch.WordTrace tailWord_3919949 prefixEnd_3919949 2012817978111388915209989 := by
  unfold tailWord_3919949
  simp only [CollatzResearch.WordTrace]
  refine ⟨142972285675701721834762901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95314857117134481223175267 142972285675701721834762901)
  ·
    refine ⟨6701825891048518211004511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142972285675701721834762901 6701825891048518211004511)
    ·
      refine ⟨10052738836572777316506767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6701825891048518211004511 10052738836572777316506767)
      ·
        refine ⟨15079108254859165974760151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10052738836572777316506767 15079108254859165974760151)
        ·
          refine ⟨22618662382288748962140227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15079108254859165974760151 22618662382288748962140227)
          ·
            refine ⟨33927993573433123443210341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22618662382288748962140227 33927993573433123443210341)
            ·
              refine ⟨6361498795018710645601939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33927993573433123443210341 6361498795018710645601939)
              ·
                refine ⟨9542248192528065968402909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361498795018710645601939 9542248192528065968402909)
                ·
                  refine ⟨3578343072198024738151091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9542248192528065968402909 3578343072198024738151091)
                  ·
                    refine ⟨5367514608297037107226637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3578343072198024738151091 5367514608297037107226637)
                    ·
                      refine ⟨2012817978111388915209989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367514608297037107226637 2012817978111388915209989)
                      ·
                        rfl

theorem cell23_3919949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3919949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3919949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3919949 prefixEnd_3919949 := by exact prefixLift 3919949
  have htrace : WordTrace (prefixWord ++ tailWord_3919949) baseStart_3919949 baseEnd_3919949 := by
    simpa [prefixWord, tailWord_3919949, baseEnd_3919949] using wordTrace_append hprefix tailTrace_3919949
  have hstable : (prefixWord ++ tailWord_3919949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3919949).length < 2 ^ (prefixWord ++ tailWord_3919949).sum := by decide
  have hdescent : baseEnd_3919949 < baseStart_3919949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3919949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920026 : List Nat := [3, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3920026 : Nat := 118140960795 + 3920026 * 2 ^ 59
def prefixEnd_3920026 : Nat := 4983230072969 + 3 ^ 40 * 3920026 * 2
def baseEnd_3920026 : Nat := 2012857516121785113947135

theorem tailTrace_3920026 : CollatzResearch.WordTrace tailWord_3920026 prefixEnd_3920026 2012857516121785113947135 := by
  unfold tailWord_3920026
  simp only [CollatzResearch.WordTrace]
  refine ⟨35743773524105690996328983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95316729397615175990210621 35743773524105690996328983)
  ·
    refine ⟨53615660286158536494493475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35743773524105690996328983 53615660286158536494493475)
    ·
      refine ⟨80423490429237804741740213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53615660286158536494493475 80423490429237804741740213)
      ·
        refine ⟨7539702227741044194538145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80423490429237804741740213 7539702227741044194538145)
        ·
          refine ⟨5654776670805783145903609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7539702227741044194538145 5654776670805783145903609)
          ·
            refine ⟨4241082503104337359427707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5654776670805783145903609 4241082503104337359427707)
            ·
              refine ⟨6361623754656506039141561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241082503104337359427707 6361623754656506039141561)
              ·
                refine ⟨4771217815992379529356171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6361623754656506039141561 4771217815992379529356171)
                ·
                  refine ⟨7156826723988569294034257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771217815992379529356171 7156826723988569294034257)
                  ·
                    refine ⟨5367620042991426970525693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7156826723988569294034257 5367620042991426970525693)
                    ·
                      refine ⟨2012857516121785113947135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367620042991426970525693 2012857516121785113947135)
                      ·
                        rfl

theorem cell23_3920026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3920026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920026 prefixEnd_3920026 := by exact prefixLift 3920026
  have htrace : WordTrace (prefixWord ++ tailWord_3920026) baseStart_3920026 baseEnd_3920026 := by
    simpa [prefixWord, tailWord_3920026, baseEnd_3920026] using wordTrace_append hprefix tailTrace_3920026
  have hstable : (prefixWord ++ tailWord_3920026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920026).length < 2 ^ (prefixWord ++ tailWord_3920026).sum := by decide
  have hdescent : baseEnd_3920026 < baseStart_3920026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920039 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_3920039 : Nat := 118140960795 + 3920039 * 2 ^ 59
def prefixEnd_3920039 : Nat := 4983230072969 + 3 ^ 40 * 3920039 * 2
def baseEnd_3920039 : Nat := 2012864191370293563084575

theorem tailTrace_3920039 : CollatzResearch.WordTrace tailWord_3920039 prefixEnd_3920039 2012864191370293563084575 := by
  unfold tailWord_3920039
  simp only [CollatzResearch.WordTrace]
  refine ⟨142975568245375667205539171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95317045496917111470359447 142975568245375667205539171)
  ·
    refine ⟨214463352368063500808308757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142975568245375667205539171 214463352368063500808308757)
    ·
      refine ⟨10052969642252976600389473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 214463352368063500808308757 10052969642252976600389473)
      ·
        refine ⟨7539727231689732450292105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10052969642252976600389473 7539727231689732450292105)
        ·
          refine ⟨5654795423767299337719079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7539727231689732450292105 5654795423767299337719079)
          ·
            refine ⟨8482193135650949006578619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5654795423767299337719079 8482193135650949006578619)
            ·
              refine ⟨12723289703476423509867929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482193135650949006578619 12723289703476423509867929)
              ·
                refine ⟨9542467277607317632400947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12723289703476423509867929 9542467277607317632400947)
                ·
                  refine ⟨14313700916410976448601421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9542467277607317632400947 14313700916410976448601421)
                  ·
                    refine ⟨5367637843654116168225533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14313700916410976448601421 5367637843654116168225533)
                    ·
                      refine ⟨2012864191370293563084575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367637843654116168225533 2012864191370293563084575)
                      ·
                        rfl

theorem cell23_3920039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_3920039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920039 prefixEnd_3920039 := by exact prefixLift 3920039
  have htrace : WordTrace (prefixWord ++ tailWord_3920039) baseStart_3920039 baseEnd_3920039 := by
    simpa [prefixWord, tailWord_3920039, baseEnd_3920039] using wordTrace_append hprefix tailTrace_3920039
  have hstable : (prefixWord ++ tailWord_3920039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920039).length < 2 ^ (prefixWord ++ tailWord_3920039).sum := by decide
  have hdescent : baseEnd_3920039 < baseStart_3920039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920075 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4]
def baseStart_3920075 : Nat := 118140960795 + 3920075 * 2 ^ 59
def prefixEnd_3920075 : Nat := 4983230072969 + 3 ^ 40 * 3920075 * 2
def baseEnd_3920075 : Nat := 2012882676673855422234409

theorem tailTrace_3920075 : CollatzResearch.WordTrace tailWord_3920075 prefixEnd_3920075 2012882676673855422234409 := by
  unfold tailWord_3920075
  simp only [CollatzResearch.WordTrace]
  refine ⟨142976881273245245353849679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95317920848830163569233119 142976881273245245353849679)
  ·
    refine ⟨214465321909867868030774519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142976881273245245353849679 214465321909867868030774519)
    ·
      refine ⟨321697982864801802046161779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214465321909867868030774519 321697982864801802046161779)
      ·
        refine ⟨482546974297202703069242669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321697982864801802046161779 482546974297202703069242669)
        ·
          refine ⟨180955115361451013650966001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482546974297202703069242669 180955115361451013650966001)
          ·
            refine ⟨135716336521088260238224501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180955115361451013650966001 135716336521088260238224501)
            ·
              refine ⟨12723406548852024397333547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135716336521088260238224501 12723406548852024397333547)
              ·
                refine ⟨19085109823278036596000321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12723406548852024397333547 19085109823278036596000321)
                ·
                  refine ⟨14313832367458527447000241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19085109823278036596000321 14313832367458527447000241)
                  ·
                    refine ⟨10735374275593895585250181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14313832367458527447000241 10735374275593895585250181)
                    ·
                      refine ⟨2012882676673855422234409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10735374275593895585250181 2012882676673855422234409)
                      ·
                        rfl

theorem cell23_3920075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_3920075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920075 prefixEnd_3920075 := by exact prefixLift 3920075
  have htrace : WordTrace (prefixWord ++ tailWord_3920075) baseStart_3920075 baseEnd_3920075 := by
    simpa [prefixWord, tailWord_3920075, baseEnd_3920075] using wordTrace_append hprefix tailTrace_3920075
  have hstable : (prefixWord ++ tailWord_3920075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920075).length < 2 ^ (prefixWord ++ tailWord_3920075).sum := by decide
  have hdescent : baseEnd_3920075 < baseStart_3920075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920079 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 2, 2, 2]
def baseStart_3920079 : Nat := 118140960795 + 3920079 * 2 ^ 59
def prefixEnd_3920079 : Nat := 4983230072969 + 3 ^ 40 * 3920079 * 2
def baseEnd_3920079 : Nat := 2012884730596473406584391

theorem tailTrace_3920079 : CollatzResearch.WordTrace tailWord_3920079 prefixEnd_3920079 2012884730596473406584391 := by
  unfold tailWord_3920079
  simp only [CollatzResearch.WordTrace]
  refine ⟨142977027165230754036995291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95318018110153836024663527 142977027165230754036995291)
  ·
    refine ⟨214465540747846131055492937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142977027165230754036995291 214465540747846131055492937)
    ·
      refine ⟨160849155560884598291619703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214465540747846131055492937 160849155560884598291619703)
      ·
        refine ⟨241273733341326897437429555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160849155560884598291619703 241273733341326897437429555)
        ·
          refine ⟨361910600011990346156144333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241273733341326897437429555 361910600011990346156144333)
          ·
            refine ⟨135716475004496379808554125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361910600011990346156144333 135716475004496379808554125)
            ·
              refine ⟨50893678126686142428207797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135716475004496379808554125 50893678126686142428207797)
              ·
                refine ⟨4771282324376825852644481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50893678126686142428207797 4771282324376825852644481)
                ·
                  refine ⟨3578461743282619389483361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771282324376825852644481 3578461743282619389483361)
                  ·
                    refine ⟨2683846307461964542112521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3578461743282619389483361 2683846307461964542112521)
                    ·
                      refine ⟨2012884730596473406584391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683846307461964542112521 2012884730596473406584391)
                      ·
                        rfl

theorem cell23_3920079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2, 2, 2].length) (baseStart_3920079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920079 prefixEnd_3920079 := by exact prefixLift 3920079
  have htrace : WordTrace (prefixWord ++ tailWord_3920079) baseStart_3920079 baseEnd_3920079 := by
    simpa [prefixWord, tailWord_3920079, baseEnd_3920079] using wordTrace_append hprefix tailTrace_3920079
  have hstable : (prefixWord ++ tailWord_3920079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920079).length < 2 ^ (prefixWord ++ tailWord_3920079).sum := by decide
  have hdescent : baseEnd_3920079 < baseStart_3920079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920095 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 3]
def baseStart_3920095 : Nat := 118140960795 + 3920095 * 2 ^ 59
def prefixEnd_3920095 : Nat := 4983230072969 + 3 ^ 40 * 3920095 * 2
def baseEnd_3920095 : Nat := 2012892946286945343984317

theorem tailTrace_3920095 : CollatzResearch.WordTrace tailWord_3920095 prefixEnd_3920095 2012892946286945343984317 := by
  unfold tailWord_3920095
  simp only [CollatzResearch.WordTrace]
  refine ⟨142977610733172788769577739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95318407155448525846385159 142977610733172788769577739)
  ·
    refine ⟨214466416099759183154366609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142977610733172788769577739 214466416099759183154366609)
    ·
      refine ⟨160849812074819387365774957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214466416099759183154366609 160849812074819387365774957)
      ·
        refine ⟨60318679528057270262165609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160849812074819387365774957 60318679528057270262165609)
        ·
          refine ⟨45239009646042952696624207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60318679528057270262165609 45239009646042952696624207)
          ·
            refine ⟨67858514469064429044936311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45239009646042952696624207 67858514469064429044936311)
            ·
              refine ⟨101787771703596643567404467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67858514469064429044936311 101787771703596643567404467)
              ·
                refine ⟨152681657555394965351106701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101787771703596643567404467 152681657555394965351106701)
                ·
                  refine ⟨57255621583273112006665013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152681657555394965351106701 57255621583273112006665013)
                  ·
                    refine ⟨5367714523431854250624845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57255621583273112006665013 5367714523431854250624845)
                    ·
                      refine ⟨2012892946286945343984317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367714523431854250624845 2012892946286945343984317)
                      ·
                        rfl

theorem cell23_3920095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_3920095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920095 prefixEnd_3920095 := by exact prefixLift 3920095
  have htrace : WordTrace (prefixWord ++ tailWord_3920095) baseStart_3920095 baseEnd_3920095 := by
    simpa [prefixWord, tailWord_3920095, baseEnd_3920095] using wordTrace_append hprefix tailTrace_3920095
  have hstable : (prefixWord ++ tailWord_3920095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920095).length < 2 ^ (prefixWord ++ tailWord_3920095).sum := by decide
  have hdescent : baseEnd_3920095 < baseStart_3920095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920115 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 4, 5]
def baseStart_3920115 : Nat := 118140960795 + 3920115 * 2 ^ 59
def prefixEnd_3920115 : Nat := 4983230072969 + 3 ^ 40 * 3920115 * 2
def baseEnd_3920115 : Nat := 670967738633345088578075

theorem tailTrace_3920115 : CollatzResearch.WordTrace tailWord_3920115 prefixEnd_3920115 670967738633345088578075 := by
  unfold tailWord_3920115
  simp only [CollatzResearch.WordTrace]
  refine ⟨142978340193100332185305799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95318893462066888123537199 142978340193100332185305799)
  ·
    refine ⟨214467510289650498277958699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142978340193100332185305799 214467510289650498277958699)
    ·
      refine ⟨321701265434475747416938049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214467510289650498277958699 321701265434475747416938049)
      ·
        refine ⟨241275949075856810562703537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321701265434475747416938049 241275949075856810562703537)
        ·
          refine ⟨180956961806892607922027653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241275949075856810562703537 180956961806892607922027653)
          ·
            refine ⟨33929430338792363985380185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180956961806892607922027653 33929430338792363985380185)
            ·
              refine ⟨25447072754094272989035139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33929430338792363985380185 25447072754094272989035139)
              ·
                refine ⟨38170609131141409483552709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25447072754094272989035139 38170609131141409483552709)
                ·
                  refine ⟨7156989212089014278166133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38170609131141409483552709 7156989212089014278166133)
                  ·
                    refine ⟨670967738633345088578075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7156989212089014278166133 670967738633345088578075)
                    ·
                      rfl

theorem cell23_3920115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 5].length) (baseStart_3920115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920115 prefixEnd_3920115 := by exact prefixLift 3920115
  have htrace : WordTrace (prefixWord ++ tailWord_3920115) baseStart_3920115 baseEnd_3920115 := by
    simpa [prefixWord, tailWord_3920115, baseEnd_3920115] using wordTrace_append hprefix tailTrace_3920115
  have hstable : (prefixWord ++ tailWord_3920115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920115).length < 2 ^ (prefixWord ++ tailWord_3920115).sum := by decide
  have hdescent : baseEnd_3920115 < baseStart_3920115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920125 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_3920125 : Nat := 118140960795 + 3920125 * 2 ^ 59
def prefixEnd_3920125 : Nat := 4983230072969 + 3 ^ 40 * 3920125 * 2
def baseEnd_3920125 : Nat := 2012908350706580226609179

theorem tailTrace_3920125 : CollatzResearch.WordTrace tailWord_3920125 prefixEnd_3920125 2012908350706580226609179 := by
  unfold tailWord_3920125
  simp only [CollatzResearch.WordTrace]
  refine ⟨142978704923064103893169829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95319136615376069262113219 142978704923064103893169829)
  ·
    refine ⟨26808507173074519479969343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142978704923064103893169829 26808507173074519479969343)
    ·
      refine ⟨40212760759611779219954015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26808507173074519479969343 40212760759611779219954015)
      ·
        refine ⟨60319141139417668829931023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40212760759611779219954015 60319141139417668829931023)
        ·
          refine ⟨90478711709126503244896535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60319141139417668829931023 90478711709126503244896535)
          ·
            refine ⟨135718067563689754867344803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90478711709126503244896535 135718067563689754867344803)
            ·
              refine ⟨203577101345534632301017205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135718067563689754867344803 203577101345534632301017205)
              ·
                refine ⟨19085353251143871778220363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203577101345534632301017205 19085353251143871778220363)
                ·
                  refine ⟨28628029876715807667330545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19085353251143871778220363 28628029876715807667330545)
                  ·
                    refine ⟨21471022407536855750497909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28628029876715807667330545 21471022407536855750497909)
                    ·
                      refine ⟨2012908350706580226609179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21471022407536855750497909 2012908350706580226609179)
                      ·
                        rfl

theorem cell23_3920125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_3920125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920125 prefixEnd_3920125 := by exact prefixLift 3920125
  have htrace : WordTrace (prefixWord ++ tailWord_3920125) baseStart_3920125 baseEnd_3920125 := by
    simpa [prefixWord, tailWord_3920125, baseEnd_3920125] using wordTrace_append hprefix tailTrace_3920125
  have hstable : (prefixWord ++ tailWord_3920125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920125).length < 2 ^ (prefixWord ++ tailWord_3920125).sum := by decide
  have hdescent : baseEnd_3920125 < baseStart_3920125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920130 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_3920130 : Nat := 118140960795 + 3920130 * 2 ^ 59
def prefixEnd_3920130 : Nat := 4983230072969 + 3 ^ 40 * 3920130 * 2
def baseEnd_3920130 : Nat := 2012910918109852707046657

theorem tailTrace_3920130 : CollatzResearch.WordTrace tailWord_3920130 prefixEnd_3920130 2012910918109852707046657 := by
  unfold tailWord_3920130
  simp only [CollatzResearch.WordTrace]
  refine ⟨35744721822011497436775461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95319258192030659831401229 35744721822011497436775461)
  ·
    refine ⟨6702135341627155769395399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35744721822011497436775461 6702135341627155769395399)
    ·
      refine ⟨10053203012440733654093099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702135341627155769395399 10053203012440733654093099)
      ·
        refine ⟨15079804518661100481139649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053203012440733654093099 15079804518661100481139649)
        ·
          refine ⟨11309853388995825360854737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15079804518661100481139649 11309853388995825360854737)
          ·
            refine ⟨8482390041746869020641053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11309853388995825360854737 8482390041746869020641053)
            ·
              refine ⟨3180896265655075882740395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8482390041746869020641053 3180896265655075882740395)
              ·
                refine ⟨4771344398482613824110593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3180896265655075882740395 4771344398482613824110593)
                ·
                  refine ⟨3578508298861960368082945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771344398482613824110593 3578508298861960368082945)
                  ·
                    refine ⟨2683881224146470276062209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3578508298861960368082945 2683881224146470276062209)
                    ·
                      refine ⟨2012910918109852707046657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683881224146470276062209 2012910918109852707046657)
                      ·
                        rfl

theorem cell23_3920130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_3920130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920130 prefixEnd_3920130 := by exact prefixLift 3920130
  have htrace : WordTrace (prefixWord ++ tailWord_3920130) baseStart_3920130 baseEnd_3920130 := by
    simpa [prefixWord, tailWord_3920130, baseEnd_3920130] using wordTrace_append hprefix tailTrace_3920130
  have hstable : (prefixWord ++ tailWord_3920130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920130).length < 2 ^ (prefixWord ++ tailWord_3920130).sum := by decide
  have hdescent : baseEnd_3920130 < baseStart_3920130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920152 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3920152 : Nat := 118140960795 + 3920152 * 2 ^ 59
def prefixEnd_3920152 : Nat := 4983230072969 + 3 ^ 40 * 3920152 * 2
def baseEnd_3920152 : Nat := 2012922214684251620971555

theorem tailTrace_3920152 : CollatzResearch.WordTrace tailWord_3920152 prefixEnd_3920152 2012922214684251620971555 := by
  unfold tailWord_3920152
  simp only [CollatzResearch.WordTrace]
  refine ⟨71489844846983143752201355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95319793129310858336268473 71489844846983143752201355)
  ·
    refine ⟨107234767270474715628302033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71489844846983143752201355 107234767270474715628302033)
    ·
      refine ⟨80426075452856036721226525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107234767270474715628302033 80426075452856036721226525)
      ·
        refine ⟨30159778294821013770459947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80426075452856036721226525 30159778294821013770459947)
        ·
          refine ⟨45239667442231520655689921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30159778294821013770459947 45239667442231520655689921)
          ·
            refine ⟨33929750581673640491767441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45239667442231520655689921 33929750581673640491767441)
            ·
              refine ⟨25447312936255230368825581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33929750581673640491767441 25447312936255230368825581)
              ·
                refine ⟨9542742351095711388309593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25447312936255230368825581 9542742351095711388309593)
                ·
                  refine ⟨7157056763321783541232195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9542742351095711388309593 7157056763321783541232195)
                  ·
                    refine ⟨10735585144982675311848293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7157056763321783541232195 10735585144982675311848293)
                    ·
                      refine ⟨2012922214684251620971555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10735585144982675311848293 2012922214684251620971555)
                      ·
                        rfl

theorem cell23_3920152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3920152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920152 prefixEnd_3920152 := by exact prefixLift 3920152
  have htrace : WordTrace (prefixWord ++ tailWord_3920152) baseStart_3920152 baseEnd_3920152 := by
    simpa [prefixWord, tailWord_3920152, baseEnd_3920152] using wordTrace_append hprefix tailTrace_3920152
  have hstable : (prefixWord ++ tailWord_3920152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920152).length < 2 ^ (prefixWord ++ tailWord_3920152).sum := by decide
  have hdescent : baseEnd_3920152 < baseStart_3920152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920172 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 3]
def baseStart_3920172 : Nat := 118140960795 + 3920172 * 2 ^ 59
def prefixEnd_3920172 : Nat := 4983230072969 + 3 ^ 40 * 3920172 * 2
def baseEnd_3920172 : Nat := 2012932484297341542721463

theorem tailTrace_3920172 : CollatzResearch.WordTrace tailWord_3920172 prefixEnd_3920172 2012932484297341542721463 := by
  unfold tailWord_3920172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71490209576946915460065385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95320279435929220613420513 71490209576946915460065385)
  ·
    refine ⟨53617657182710186595049039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71490209576946915460065385 53617657182710186595049039)
    ·
      refine ⟨80426485774065279892573559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53617657182710186595049039 80426485774065279892573559)
      ·
        refine ⟨120639728661097919838860339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80426485774065279892573559 120639728661097919838860339)
        ·
          refine ⟨180959592991646879758290509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120639728661097919838860339 180959592991646879758290509)
          ·
            refine ⟨67859847371867579909358941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180959592991646879758290509 67859847371867579909358941)
            ·
              refine ⟨25447442764450342466009603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67859847371867579909358941 25447442764450342466009603)
              ·
                refine ⟨38171164146675513699014405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25447442764450342466009603 38171164146675513699014405)
                ·
                  refine ⟨7157093277501658818565201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38171164146675513699014405 7157093277501658818565201)
                  ·
                    refine ⟨5367819958126244113923901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7157093277501658818565201 5367819958126244113923901)
                    ·
                      refine ⟨2012932484297341542721463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367819958126244113923901 2012932484297341542721463)
                      ·
                        rfl

theorem cell23_3920172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_3920172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920172 prefixEnd_3920172 := by exact prefixLift 3920172
  have htrace : WordTrace (prefixWord ++ tailWord_3920172) baseStart_3920172 baseEnd_3920172 := by
    simpa [prefixWord, tailWord_3920172, baseEnd_3920172] using wordTrace_append hprefix tailTrace_3920172
  have hstable : (prefixWord ++ tailWord_3920172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920172).length < 2 ^ (prefixWord ++ tailWord_3920172).sum := by decide
  have hdescent : baseEnd_3920172 < baseStart_3920172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920175 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 8]
def baseStart_3920175 : Nat := 118140960795 + 3920175 * 2 ^ 59
def prefixEnd_3920175 : Nat := 4983230072969 + 3 ^ 40 * 3920175 * 2
def baseEnd_3920175 : Nat := 223659336082145003442661

theorem tailTrace_3920175 : CollatzResearch.WordTrace tailWord_3920175 prefixEnd_3920175 223659336082145003442661 := by
  unfold tailWord_3920175
  simp only [CollatzResearch.WordTrace]
  refine ⟨142980528572882962432489979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95320352381921974954993319 142980528572882962432489979)
  ·
    refine ⟨214470792859324443648734969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142980528572882962432489979 214470792859324443648734969)
    ·
      refine ⟨160853094644493332736551227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214470792859324443648734969 160853094644493332736551227)
      ·
        refine ⟨241279641966739999104826841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160853094644493332736551227 241279641966739999104826841)
        ·
          refine ⟨180959731475054999328620131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241279641966739999104826841 180959731475054999328620131)
          ·
            refine ⟨271439597212582498992930197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180959731475054999328620131 271439597212582498992930197)
            ·
              refine ⟨12723731119339804640293603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271439597212582498992930197 12723731119339804640293603)
              ·
                refine ⟨19085596679009706960440405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12723731119339804640293603 19085596679009706960440405)
                ·
                  refine ⟨223659336082145003442661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19085596679009706960440405 223659336082145003442661)
                  ·
                    rfl

theorem cell23_3920175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 8].length) (baseStart_3920175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920175 prefixEnd_3920175 := by exact prefixLift 3920175
  have htrace : WordTrace (prefixWord ++ tailWord_3920175) baseStart_3920175 baseEnd_3920175 := by
    simpa [prefixWord, tailWord_3920175, baseEnd_3920175] using wordTrace_append hprefix tailTrace_3920175
  have hstable : (prefixWord ++ tailWord_3920175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920175).length < 2 ^ (prefixWord ++ tailWord_3920175).sum := by decide
  have hdescent : baseEnd_3920175 < baseStart_3920175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920195 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6]
def baseStart_3920195 : Nat := 118140960795 + 3920195 * 2 ^ 59
def prefixEnd_3920195 : Nat := 4983230072969 + 3 ^ 40 * 3920195 * 2
def baseEnd_3920195 : Nat := 2012944294352394952733857

theorem tailTrace_3920195 : CollatzResearch.WordTrace tailWord_3920195 prefixEnd_3920195 2012944294352394952733857 := by
  unfold tailWord_3920195
  simp only [CollatzResearch.WordTrace]
  refine ⟨142981258032810505848218039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95320838688540337232145359 142981258032810505848218039)
  ·
    refine ⟨214471887049215758772327059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142981258032810505848218039 214471887049215758772327059)
    ·
      refine ⟨321707830573823638158490589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214471887049215758772327059 321707830573823638158490589)
      ·
        refine ⟨120640436465183864309433971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321707830573823638158490589 120640436465183864309433971)
        ·
          refine ⟨180960654697775796464150957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120640436465183864309433971 180960654697775796464150957)
          ·
            refine ⟨67860245511665923674056609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180960654697775796464150957 67860245511665923674056609)
            ·
              refine ⟨50895184133749442755542457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67860245511665923674056609 50895184133749442755542457)
              ·
                refine ⟨38171388100312082066656843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50895184133749442755542457 38171388100312082066656843)
                ·
                  refine ⟨57257082150468123099985265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38171388100312082066656843 57257082150468123099985265)
                  ·
                    refine ⟨42942811612851092324988949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57257082150468123099985265 42942811612851092324988949)
                    ·
                      refine ⟨2012944294352394952733857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42942811612851092324988949 2012944294352394952733857)
                      ·
                        rfl

theorem cell23_3920195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_3920195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920195 prefixEnd_3920195 := by exact prefixLift 3920195
  have htrace : WordTrace (prefixWord ++ tailWord_3920195) baseStart_3920195 baseEnd_3920195 := by
    simpa [prefixWord, tailWord_3920195, baseEnd_3920195] using wordTrace_append hprefix tailTrace_3920195
  have hstable : (prefixWord ++ tailWord_3920195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920195).length < 2 ^ (prefixWord ++ tailWord_3920195).sum := by decide
  have hdescent : baseEnd_3920195 < baseStart_3920195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920270 : List Nat := [4, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3920270 : Nat := 118140960795 + 3920270 * 2 ^ 59
def prefixEnd_3920270 : Nat := 4983230072969 + 3 ^ 40 * 3920270 * 2
def baseEnd_3920270 : Nat := 2012982805401482159296013

theorem tailTrace_3920270 : CollatzResearch.WordTrace tailWord_3920270 prefixEnd_3920270 2012982805401482159296013 := by
  unfold tailWord_3920270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872999188442349207149783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95322662338359195771465509 17872999188442349207149783)
  ·
    refine ⟨26809498782663523810724675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17872999188442349207149783 26809498782663523810724675)
    ·
      refine ⟨40214248173995285716087013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26809498782663523810724675 40214248173995285716087013)
      ·
        refine ⟨7540171532624116071766315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40214248173995285716087013 7540171532624116071766315)
        ·
          refine ⟨11310257298936174107649473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540171532624116071766315 11310257298936174107649473)
          ·
            refine ⟨8482692974202130580737105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11310257298936174107649473 8482692974202130580737105)
            ·
              refine ⟨6362019730651597935552829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8482692974202130580737105 6362019730651597935552829)
              ·
                refine ⟨2385757398994349225832311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6362019730651597935552829 2385757398994349225832311)
                ·
                  refine ⟨3578636098491523838748467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385757398994349225832311 3578636098491523838748467)
                  ·
                    refine ⟨5367954147737285758122701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3578636098491523838748467 5367954147737285758122701)
                    ·
                      refine ⟨2012982805401482159296013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5367954147737285758122701 2012982805401482159296013)
                      ·
                        rfl

theorem cell23_3920270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3920270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920270 prefixEnd_3920270 := by exact prefixLift 3920270
  have htrace : WordTrace (prefixWord ++ tailWord_3920270) baseStart_3920270 baseEnd_3920270 := by
    simpa [prefixWord, tailWord_3920270, baseEnd_3920270] using wordTrace_append hprefix tailTrace_3920270
  have hstable : (prefixWord ++ tailWord_3920270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920270).length < 2 ^ (prefixWord ++ tailWord_3920270).sum := by decide
  have hdescent : baseEnd_3920270 < baseStart_3920270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920282 : List Nat := [3, 1, 1, 4, 1, 3, 10]
def baseStart_3920282 : Nat := 118140960795 + 3920282 * 2 ^ 59
def prefixEnd_3920282 : Nat := 4983230072969 + 3 ^ 40 * 3920282 * 2
def baseEnd_3920282 : Nat := 24851715644065877930197

theorem tailTrace_3920282 : CollatzResearch.WordTrace tailWord_3920282 prefixEnd_3920282 24851715644065877930197 := by
  unfold tailWord_3920282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35746107795873829926658775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95322954122330213137756733 35746107795873829926658775)
  ·
    refine ⟨53619161693810744889988163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35746107795873829926658775 53619161693810744889988163)
    ·
      refine ⟨80428742540716117334982245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53619161693810744889988163 80428742540716117334982245)
      ·
        refine ⟨15080389226384272000309171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80428742540716117334982245 15080389226384272000309171)
        ·
          refine ⟨22620583839576408000463757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15080389226384272000309171 22620583839576408000463757)
          ·
            refine ⟨8482718939841153000173909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22620583839576408000463757 8482718939841153000173909)
            ·
              refine ⟨24851715644065877930197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8482718939841153000173909 24851715644065877930197)
              ·
                rfl

theorem cell23_3920282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 10].length) (baseStart_3920282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920282 prefixEnd_3920282 := by exact prefixLift 3920282
  have htrace : WordTrace (prefixWord ++ tailWord_3920282) baseStart_3920282 baseEnd_3920282 := by
    simpa [prefixWord, tailWord_3920282, baseEnd_3920282] using wordTrace_append hprefix tailTrace_3920282
  have hstable : (prefixWord ++ tailWord_3920282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920282).length < 2 ^ (prefixWord ++ tailWord_3920282).sum := by decide
  have hdescent : baseEnd_3920282 < baseStart_3920282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920293 : List Nat := [1, 3, 1, 2, 1, 1, 3, 6, 1, 2, 2]
def baseStart_3920293 : Nat := 118140960795 + 3920293 * 2 ^ 59
def prefixEnd_3920293 : Nat := 4983230072969 + 3 ^ 40 * 3920293 * 2
def baseEnd_3920293 : Nat := 2012994615456535569308407

theorem tailTrace_3920293 : CollatzResearch.WordTrace tailWord_3920293 prefixEnd_3920293 2012994615456535569308407 := by
  unfold tailWord_3920293
  simp only [CollatzResearch.WordTrace]
  refine ⟨142984832386455468585285533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95323221590970312390190355 142984832386455468585285533)
  ·
    refine ⟨53619312144920800719482075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142984832386455468585285533 53619312144920800719482075)
    ·
      refine ⟨80428968217381201079223113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53619312144920800719482075 80428968217381201079223113)
      ·
        refine ⟨60321726163035900809417335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80428968217381201079223113 60321726163035900809417335)
        ·
          refine ⟨90482589244553851214126003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60321726163035900809417335 90482589244553851214126003)
          ·
            refine ⟨135723883866830776821189005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90482589244553851214126003 135723883866830776821189005)
            ·
              refine ⟨50896456450061541307945877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135723883866830776821189005 50896456450061541307945877)
              ·
                refine ⟨2385771396096634748809963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50896456450061541307945877 2385771396096634748809963)
                ·
                  refine ⟨3578657094144952123214945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385771396096634748809963 3578657094144952123214945)
                  ·
                    refine ⟨2683992820608714092411209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3578657094144952123214945 2683992820608714092411209)
                    ·
                      refine ⟨2012994615456535569308407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2683992820608714092411209 2012994615456535569308407)
                      ·
                        rfl

theorem cell23_3920293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_3920293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920293 prefixEnd_3920293 := by exact prefixLift 3920293
  have htrace : WordTrace (prefixWord ++ tailWord_3920293) baseStart_3920293 baseEnd_3920293 := by
    simpa [prefixWord, tailWord_3920293, baseEnd_3920293] using wordTrace_append hprefix tailTrace_3920293
  have hstable : (prefixWord ++ tailWord_3920293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920293).length < 2 ^ (prefixWord ++ tailWord_3920293).sum := by decide
  have hdescent : baseEnd_3920293 < baseStart_3920293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920296 : List Nat := [2, 1, 6, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3920296 : Nat := 118140960795 + 3920296 * 2 ^ 59
def prefixEnd_3920296 : Nat := 4983230072969 + 3 ^ 40 * 3920296 * 2
def baseEnd_3920296 : Nat := 2012996155898499057570893

theorem tailTrace_3920296 : CollatzResearch.WordTrace tailWord_3920296 prefixEnd_3920296 2012996155898499057570893 := by
  unfold tailWord_3920296
  simp only [CollatzResearch.WordTrace]
  refine ⟨71492470902722300048822371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95323294536963066731763161 71492470902722300048822371)
  ·
    refine ⟨107238706354083450073233557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71492470902722300048822371 107238706354083450073233557)
    ·
      refine ⟨5026814360347661722182823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107238706354083450073233557 5026814360347661722182823)
      ·
        refine ⟨7540221540521492583274235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5026814360347661722182823 7540221540521492583274235)
        ·
          refine ⟨11310332310782238874911353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540221540521492583274235 11310332310782238874911353)
          ·
            refine ⟨8482749233086679156183515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11310332310782238874911353 8482749233086679156183515)
            ·
              refine ⟨12724123849630018734275273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482749233086679156183515 12724123849630018734275273)
              ·
                refine ⟨9543092887222514050706455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12724123849630018734275273 9543092887222514050706455)
                ·
                  refine ⟨14314639330833771076059683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9543092887222514050706455 14314639330833771076059683)
                  ·
                    refine ⟨21471958996250656614089525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14314639330833771076059683 21471958996250656614089525)
                    ·
                      refine ⟨2012996155898499057570893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21471958996250656614089525 2012996155898499057570893)
                      ·
                        rfl

theorem cell23_3920296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3920296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920296 prefixEnd_3920296 := by exact prefixLift 3920296
  have htrace : WordTrace (prefixWord ++ tailWord_3920296) baseStart_3920296 baseEnd_3920296 := by
    simpa [prefixWord, tailWord_3920296, baseEnd_3920296] using wordTrace_append hprefix tailTrace_3920296
  have hstable : (prefixWord ++ tailWord_3920296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920296).length < 2 ^ (prefixWord ++ tailWord_3920296).sum := by decide
  have hdescent : baseEnd_3920296 < baseStart_3920296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920316 : List Nat := [2, 2, 2, 4, 1, 3, 2, 7]
def baseStart_3920316 : Nat := 118140960795 + 3920316 * 2 ^ 59
def prefixEnd_3920316 : Nat := 4983230072969 + 3 ^ 40 * 3920316 * 2
def baseEnd_3920316 : Nat := 74555793537466258493363

theorem tailTrace_3920316 : CollatzResearch.WordTrace tailWord_3920316 prefixEnd_3920316 74555793537466258493363 := by
  unfold tailWord_3920316
  simp only [CollatzResearch.WordTrace]
  refine ⟨71492835632686071756686401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95323780843581429008915201 71492835632686071756686401)
  ·
    refine ⟨53619626724514553817514801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71492835632686071756686401 53619626724514553817514801)
    ·
      refine ⟨40214720043385915363136101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53619626724514553817514801 40214720043385915363136101)
      ·
        refine ⟨7540260008134859130588019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40214720043385915363136101 7540260008134859130588019)
        ·
          refine ⟨11310390012202288695882029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540260008134859130588019 11310390012202288695882029)
          ·
            refine ⟨4241396254575858260955761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11310390012202288695882029 4241396254575858260955761)
            ·
              refine ⟨3181047190931893695716821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241396254575858260955761 3181047190931893695716821)
              ·
                refine ⟨74555793537466258493363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3181047190931893695716821 74555793537466258493363)
                ·
                  rfl

theorem cell23_3920316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 7].length) (baseStart_3920316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920316 prefixEnd_3920316 := by exact prefixLift 3920316
  have htrace : WordTrace (prefixWord ++ tailWord_3920316) baseStart_3920316 baseEnd_3920316 := by
    simpa [prefixWord, tailWord_3920316, baseEnd_3920316] using wordTrace_append hprefix tailTrace_3920316
  have hstable : (prefixWord ++ tailWord_3920316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920316).length < 2 ^ (prefixWord ++ tailWord_3920316).sum := by decide
  have hdescent : baseEnd_3920316 < baseStart_3920316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920321 : List Nat := [1, 2, 7, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3920321 : Nat := 118140960795 + 3920321 * 2 ^ 59
def prefixEnd_3920321 : Nat := 4983230072969 + 3 ^ 40 * 3920321 * 2
def baseEnd_3920321 : Nat := 2013008992914861459758279

theorem tailTrace_3920321 : CollatzResearch.WordTrace tailWord_3920321 prefixEnd_3920321 2013008992914861459758279 := by
  unfold tailWord_3920321
  simp only [CollatzResearch.WordTrace]
  refine ⟨142985853630354029367304817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95323902420236019578203211 142985853630354029367304817)
  ·
    refine ⟨107239390222765522025478613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142985853630354029367304817 107239390222765522025478613)
    ·
      refine ⟨2513423208346066922472155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 107239390222765522025478613 2513423208346066922472155)
      ·
        refine ⟨3770134812519100383708233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2513423208346066922472155 3770134812519100383708233)
        ·
          refine ⟨2827601109389325287781175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770134812519100383708233 2827601109389325287781175)
          ·
            refine ⟨4241401664083987931671763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827601109389325287781175 4241401664083987931671763)
            ·
              refine ⟨6362102496125981897507645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241401664083987931671763 6362102496125981897507645)
              ·
                refine ⟨2385788436047243211565367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6362102496125981897507645 2385788436047243211565367)
                ·
                  refine ⟨3578682654070864817348051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2385788436047243211565367 3578682654070864817348051)
                  ·
                    refine ⟨5368023981106297226022077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3578682654070864817348051 5368023981106297226022077)
                    ·
                      refine ⟨2013008992914861459758279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5368023981106297226022077 2013008992914861459758279)
                      ·
                        rfl

theorem cell23_3920321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3920321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920321 prefixEnd_3920321 := by exact prefixLift 3920321
  have htrace : WordTrace (prefixWord ++ tailWord_3920321) baseStart_3920321 baseEnd_3920321 := by
    simpa [prefixWord, tailWord_3920321, baseEnd_3920321] using wordTrace_append hprefix tailTrace_3920321
  have hstable : (prefixWord ++ tailWord_3920321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920321).length < 2 ^ (prefixWord ++ tailWord_3920321).sum := by decide
  have hdescent : baseEnd_3920321 < baseStart_3920321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920349 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3920349 : Nat := 118140960795 + 3920349 * 2 ^ 59
def prefixEnd_3920349 : Nat := 4983230072969 + 3 ^ 40 * 3920349 * 2
def baseEnd_3920349 : Nat := 2013023370373187350208149

theorem tailTrace_3920349 : CollatzResearch.WordTrace tailWord_3920349 prefixEnd_3920349 2013023370373187350208149 := by
  unfold tailWord_3920349
  simp only [CollatzResearch.WordTrace]
  refine ⟨142986874874252590149324101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95324583249501726766216067 142986874874252590149324101)
  ·
    refine ⟨26810039038922360652998269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142986874874252590149324101 26810039038922360652998269)
    ·
      refine ⟨10053764639595885244874351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26810039038922360652998269 10053764639595885244874351)
      ·
        refine ⟨15080646959393827867311527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053764639595885244874351 15080646959393827867311527)
        ·
          refine ⟨22620970439090741800967291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15080646959393827867311527 22620970439090741800967291)
          ·
            refine ⟨33931455658636112701450937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22620970439090741800967291 33931455658636112701450937)
            ·
              refine ⟨25448591743977084526088203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33931455658636112701450937 25448591743977084526088203)
              ·
                refine ⟨38172887615965626789132305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25448591743977084526088203 38172887615965626789132305)
                ·
                  refine ⟨28629665711974220091849229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38172887615965626789132305 28629665711974220091849229)
                  ·
                    refine ⟨10736124641990332534443461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28629665711974220091849229 10736124641990332534443461)
                    ·
                      refine ⟨2013023370373187350208149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10736124641990332534443461 2013023370373187350208149)
                      ·
                        rfl

theorem cell23_3920349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3920349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920349 prefixEnd_3920349 := by exact prefixLift 3920349
  have htrace : WordTrace (prefixWord ++ tailWord_3920349) baseStart_3920349 baseEnd_3920349 := by
    simpa [prefixWord, tailWord_3920349, baseEnd_3920349] using wordTrace_append hprefix tailTrace_3920349
  have hstable : (prefixWord ++ tailWord_3920349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920349).length < 2 ^ (prefixWord ++ tailWord_3920349).sum := by decide
  have hdescent : baseEnd_3920349 < baseStart_3920349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920352 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_3920352 : Nat := 118140960795 + 3920352 * 2 ^ 59
def prefixEnd_3920352 : Nat := 4983230072969 + 3 ^ 40 * 3920352 * 2
def baseEnd_3920352 : Nat := 2013024910815150838470635

theorem tailTrace_3920352 : CollatzResearch.WordTrace tailWord_3920352 prefixEnd_3920352 2013024910815150838470635 := by
  unfold tailWord_3920352
  simp only [CollatzResearch.WordTrace]
  refine ⟨71493492146620860830841655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95324656195494481107788873 71493492146620860830841655)
  ·
    refine ⟨107240238219931291246262483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71493492146620860830841655 107240238219931291246262483)
    ·
      refine ⟨160860357329896936869393725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107240238219931291246262483 160860357329896936869393725)
      ·
        refine ⟨60322633998711351326022647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160860357329896936869393725 60322633998711351326022647)
        ·
          refine ⟨90483950998067026989033971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60322633998711351326022647 90483950998067026989033971)
          ·
            refine ⟨135725926497100540483550957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90483950998067026989033971 135725926497100540483550957)
            ·
              refine ⟨50897222436412702681331609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135725926497100540483550957 50897222436412702681331609)
              ·
                refine ⟨38172916827309527010998707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50897222436412702681331609 38172916827309527010998707)
                ·
                  refine ⟨57259375240964290516498061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38172916827309527010998707 57259375240964290516498061)
                  ·
                    refine ⟨21472265715361608943686773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57259375240964290516498061 21472265715361608943686773)
                    ·
                      refine ⟨2013024910815150838470635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21472265715361608943686773 2013024910815150838470635)
                      ·
                        rfl

theorem cell23_3920352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_3920352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920352 prefixEnd_3920352 := by exact prefixLift 3920352
  have htrace : WordTrace (prefixWord ++ tailWord_3920352) baseStart_3920352 baseEnd_3920352 := by
    simpa [prefixWord, tailWord_3920352, baseEnd_3920352] using wordTrace_append hprefix tailTrace_3920352
  have hstable : (prefixWord ++ tailWord_3920352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920352).length < 2 ^ (prefixWord ++ tailWord_3920352).sum := by decide
  have hdescent : baseEnd_3920352 < baseStart_3920352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920354 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3920354 : Nat := 118140960795 + 3920354 * 2 ^ 59
def prefixEnd_3920354 : Nat := 4983230072969 + 3 ^ 40 * 3920354 * 2
def baseEnd_3920354 : Nat := 671008645925486610215209

theorem tailTrace_3920354 : CollatzResearch.WordTrace tailWord_3920354 prefixEnd_3920354 671008645925486610215209 := by
  unfold tailWord_3920354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35746764309808619000814029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95324704826156317335504077 35746764309808619000814029)
  ·
    refine ⟨13405036616178232125305261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35746764309808619000814029 13405036616178232125305261)
    ·
      refine ⟨5026888731066837046989473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13405036616178232125305261 5026888731066837046989473)
      ·
        refine ⟨3770166548300127785242105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5026888731066837046989473 3770166548300127785242105)
        ·
          refine ⟨2827624911225095838931579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770166548300127785242105 2827624911225095838931579)
          ·
            refine ⟨4241437366837643758397369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827624911225095838931579 4241437366837643758397369)
            ·
              refine ⟨3181078025128232818798027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241437366837643758397369 3181078025128232818798027)
              ·
                refine ⟨4771617037692349228197041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181078025128232818798027 4771617037692349228197041)
                ·
                  refine ⟨3578712778269261921147781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771617037692349228197041 3578712778269261921147781)
                  ·
                    refine ⟨671008645925486610215209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3578712778269261921147781 671008645925486610215209)
                    ·
                      rfl

theorem cell23_3920354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3920354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920354 prefixEnd_3920354 := by exact prefixLift 3920354
  have htrace : WordTrace (prefixWord ++ tailWord_3920354) baseStart_3920354 baseEnd_3920354 := by
    simpa [prefixWord, tailWord_3920354, baseEnd_3920354] using wordTrace_append hprefix tailTrace_3920354
  have hstable : (prefixWord ++ tailWord_3920354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920354).length < 2 ^ (prefixWord ++ tailWord_3920354).sum := by decide
  have hdescent : baseEnd_3920354 < baseStart_3920354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920360 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_3920360 : Nat := 118140960795 + 3920360 * 2 ^ 59
def prefixEnd_3920360 : Nat := 4983230072969 + 3 ^ 40 * 3920360 * 2
def baseEnd_3920360 : Nat := 2013029018660386807170599

theorem tailTrace_3920360 : CollatzResearch.WordTrace tailWord_3920360 prefixEnd_3920360 2013029018660386807170599 := by
  unfold tailWord_3920360
  simp only [CollatzResearch.WordTrace]
  refine ⟨71493638038606369513987267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95324850718141826018649689 71493638038606369513987267)
  ·
    refine ⟨107240457057909554270980901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71493638038606369513987267 107240457057909554270980901)
    ·
      refine ⟨20107585698358041425808919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107240457057909554270980901 20107585698358041425808919)
      ·
        refine ⟨30161378547537062138713379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20107585698358041425808919 30161378547537062138713379)
        ·
          refine ⟨45242067821305593208070069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30161378547537062138713379 45242067821305593208070069)
          ·
            refine ⟨4241443858247399363256569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45242067821305593208070069 4241443858247399363256569)
            ·
              refine ⟨3181082893685549522442427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241443858247399363256569 3181082893685549522442427)
              ·
                refine ⟨4771624340528324283663641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181082893685549522442427 4771624340528324283663641)
                ·
                  refine ⟨3578718255396243212747731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771624340528324283663641 3578718255396243212747731)
                  ·
                    refine ⟨5368077383094364819121597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3578718255396243212747731 5368077383094364819121597)
                    ·
                      refine ⟨2013029018660386807170599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5368077383094364819121597 2013029018660386807170599)
                      ·
                        rfl

theorem cell23_3920360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_3920360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920360 prefixEnd_3920360 := by exact prefixLift 3920360
  have htrace : WordTrace (prefixWord ++ tailWord_3920360) baseStart_3920360 baseEnd_3920360 := by
    simpa [prefixWord, tailWord_3920360, baseEnd_3920360] using wordTrace_append hprefix tailTrace_3920360
  have hstable : (prefixWord ++ tailWord_3920360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920360).length < 2 ^ (prefixWord ++ tailWord_3920360).sum := by decide
  have hdescent : baseEnd_3920360 < baseStart_3920360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920423 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 7]
def baseStart_3920423 : Nat := 118140960795 + 3920423 * 2 ^ 59
def prefixEnd_3920423 : Nat := 4983230072969 + 3 ^ 40 * 3920423 * 2
def baseEnd_3920423 : Nat := 223673485326846673409201

theorem tailTrace_3920423 : CollatzResearch.WordTrace tailWord_3920423 prefixEnd_3920423 223673485326846673409201 := by
  unfold tailWord_3920423
  simp only [CollatzResearch.WordTrace]
  refine ⟨142989573875984500787517923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95326382583989667191678615 142989573875984500787517923)
  ·
    refine ⟨214484360813976751181276885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142989573875984500787517923 214484360813976751181276885)
    ·
      refine ⟨5026977206577580105811177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 214484360813976751181276885 5026977206577580105811177)
      ·
        refine ⟨3770232904933185079358383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5026977206577580105811177 3770232904933185079358383)
        ·
          refine ⟨5655349357399777619037575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3770232904933185079358383 5655349357399777619037575)
          ·
            refine ⟨8483024036099666428556363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655349357399777619037575 8483024036099666428556363)
            ·
              refine ⟨12724536054149499642834545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8483024036099666428556363 12724536054149499642834545)
              ·
                refine ⟨9543402040612124732125909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12724536054149499642834545 9543402040612124732125909)
                ·
                  refine ⟨223673485326846673409201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9543402040612124732125909 223673485326846673409201)
                  ·
                    rfl

theorem cell23_3920423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 7].length) (baseStart_3920423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920423 prefixEnd_3920423 := by exact prefixLift 3920423
  have htrace : WordTrace (prefixWord ++ tailWord_3920423) baseStart_3920423 baseEnd_3920423 := by
    simpa [prefixWord, tailWord_3920423, baseEnd_3920423] using wordTrace_append hprefix tailTrace_3920423
  have hstable : (prefixWord ++ tailWord_3920423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920423).length < 2 ^ (prefixWord ++ tailWord_3920423).sum := by decide
  have hdescent : baseEnd_3920423 < baseStart_3920423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920439 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_3920439 : Nat := 118140960795 + 3920439 * 2 ^ 59
def prefixEnd_3920439 : Nat := 4983230072969 + 3 ^ 40 * 3920439 * 2
def baseEnd_3920439 : Nat := 2013069583632091998082735

theorem tailTrace_3920439 : CollatzResearch.WordTrace tailWord_3920439 prefixEnd_3920439 2013069583632091998082735 := by
  unfold tailWord_3920439
  simp only [CollatzResearch.WordTrace]
  refine ⟨142990157443926535520100371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95326771629284357013400247 142990157443926535520100371)
  ·
    refine ⟨214485236165889803280150557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142990157443926535520100371 214485236165889803280150557)
    ·
      refine ⟨80431963562208676230056459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214485236165889803280150557 80431963562208676230056459)
      ·
        refine ⟨120647945343313014345084689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80431963562208676230056459 120647945343313014345084689)
        ·
          refine ⟨90485959007484760758813517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120647945343313014345084689 90485959007484760758813517)
          ·
            refine ⟨33932234627806785284555069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90485959007484760758813517 33932234627806785284555069)
            ·
              refine ⟨12724587985427544481708151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33932234627806785284555069 12724587985427544481708151)
              ·
                refine ⟨19086881978141316722562227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12724587985427544481708151 19086881978141316722562227)
                ·
                  refine ⟨28630322967211975083843341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19086881978141316722562227 28630322967211975083843341)
                  ·
                    refine ⟨10736371112704490656441253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28630322967211975083843341 10736371112704490656441253)
                    ·
                      refine ⟨2013069583632091998082735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10736371112704490656441253 2013069583632091998082735)
                      ·
                        rfl

theorem cell23_3920439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_3920439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920439 prefixEnd_3920439 := by exact prefixLift 3920439
  have htrace : WordTrace (prefixWord ++ tailWord_3920439) baseStart_3920439 baseEnd_3920439 := by
    simpa [prefixWord, tailWord_3920439, baseEnd_3920439] using wordTrace_append hprefix tailTrace_3920439
  have hstable : (prefixWord ++ tailWord_3920439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920439).length < 2 ^ (prefixWord ++ tailWord_3920439).sum := by decide
  have hdescent : baseEnd_3920439 < baseStart_3920439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920479 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 6]
def baseStart_3920479 : Nat := 118140960795 + 3920479 * 2 ^ 59
def prefixEnd_3920479 : Nat := 4983230072969 + 3 ^ 40 * 3920479 * 2
def baseEnd_3920479 : Nat := 223676680317585760175839

theorem tailTrace_3920479 : CollatzResearch.WordTrace tailWord_3920479 prefixEnd_3920479 223676680317585760175839 := by
  unfold tailWord_3920479
  simp only [CollatzResearch.WordTrace]
  refine ⟨142991616363781622351556491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95327744242521081567704327 142991616363781622351556491)
  ·
    refine ⟨214487424545672433527334737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142991616363781622351556491 214487424545672433527334737)
    ·
      refine ⟨160865568409254325145501053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214487424545672433527334737 160865568409254325145501053)
      ·
        refine ⟨60324588153470371929562895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160865568409254325145501053 60324588153470371929562895)
        ·
          refine ⟨90486882230205557894344343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60324588153470371929562895 90486882230205557894344343)
          ·
            refine ⟨135730323345308336841516515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90486882230205557894344343 135730323345308336841516515)
            ·
              refine ⟨203595485017962505262274773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135730323345308336841516515 203595485017962505262274773)
              ·
                refine ⟨4771769180108496217084565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203595485017962505262274773 4771769180108496217084565)
                ·
                  refine ⟨223676680317585760175839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4771769180108496217084565 223676680317585760175839)
                  ·
                    rfl

theorem cell23_3920479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 6].length) (baseStart_3920479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920479 prefixEnd_3920479 := by exact prefixLift 3920479
  have htrace : WordTrace (prefixWord ++ tailWord_3920479) baseStart_3920479 baseEnd_3920479 := by
    simpa [prefixWord, tailWord_3920479, baseEnd_3920479] using wordTrace_append hprefix tailTrace_3920479
  have hstable : (prefixWord ++ tailWord_3920479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920479).length < 2 ^ (prefixWord ++ tailWord_3920479).sum := by decide
  have hdescent : baseEnd_3920479 < baseStart_3920479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920489 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 3]
def baseStart_3920489 : Nat := 118140960795 + 3920489 * 2 ^ 59
def prefixEnd_3920489 : Nat := 4983230072969 + 3 ^ 40 * 3920489 * 2
def baseEnd_3920489 : Nat := 2013095257664816802457505

theorem tailTrace_3920489 : CollatzResearch.WordTrace tailWord_3920489 prefixEnd_3920489 2013095257664816802457505 := by
  unfold tailWord_3920489
  simp only [CollatzResearch.WordTrace]
  refine ⟨142991981093745394059420521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95327987395830262706280347 142991981093745394059420521)
  ·
    refine ⟨107243985820309045544565391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142991981093745394059420521 107243985820309045544565391)
    ·
      refine ⟨160865978730463568316848087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107243985820309045544565391 160865978730463568316848087)
      ·
        refine ⟨241298968095695352475272131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160865978730463568316848087 241298968095695352475272131)
        ·
          refine ⟨361948452143543028712908197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241298968095695352475272131 361948452143543028712908197)
          ·
            refine ⟨67865334776914317883670287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361948452143543028712908197 67865334776914317883670287)
            ·
              refine ⟨101798002165371476825505431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67865334776914317883670287 101798002165371476825505431)
              ·
                refine ⟨152697003248057215238258147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101798002165371476825505431 152697003248057215238258147)
                ·
                  refine ⟨229045504872085822857387221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152697003248057215238258147 229045504872085822857387221)
                  ·
                    refine ⟨5368254020439511473220013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 229045504872085822857387221 5368254020439511473220013)
                    ·
                      refine ⟨2013095257664816802457505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5368254020439511473220013 2013095257664816802457505)
                      ·
                        rfl

theorem cell23_3920489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_3920489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920489 prefixEnd_3920489 := by exact prefixLift 3920489
  have htrace : WordTrace (prefixWord ++ tailWord_3920489) baseStart_3920489 baseEnd_3920489 := by
    simpa [prefixWord, tailWord_3920489, baseEnd_3920489] using wordTrace_append hprefix tailTrace_3920489
  have hstable : (prefixWord ++ tailWord_3920489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920489).length < 2 ^ (prefixWord ++ tailWord_3920489).sum := by decide
  have hdescent : baseEnd_3920489 < baseStart_3920489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920526 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3920526 : Nat := 118140960795 + 3920526 * 2 ^ 59
def prefixEnd_3920526 : Nat := 4983230072969 + 3 ^ 40 * 3920526 * 2
def baseEnd_3920526 : Nat := 671038085483011052564945

theorem tailTrace_3920526 : CollatzResearch.WordTrace tailWord_3920526 prefixEnd_3920526 671038085483011052564945 := by
  unfold tailWord_3920526
  simp only [CollatzResearch.WordTrace]
  refine ⟨17874166324326418672314679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95328887063074232919011621 17874166324326418672314679)
  ·
    refine ⟨26811249486489628008472019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17874166324326418672314679 26811249486489628008472019)
    ·
      refine ⟨40216874229734442012708029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26811249486489628008472019 40216874229734442012708029)
      ·
        refine ⟨15081327836150415754765511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40216874229734442012708029 15081327836150415754765511)
        ·
          refine ⟨22621991754225623632148267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15081327836150415754765511 22621991754225623632148267)
          ·
            refine ⟨33932987631338435448222401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22621991754225623632148267 33932987631338435448222401)
            ·
              refine ⟨25449740723503826586166801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33932987631338435448222401 25449740723503826586166801)
              ·
                refine ⟨19087305542627869939625101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25449740723503826586166801 19087305542627869939625101)
                ·
                  refine ⟨7157739578485451227359413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19087305542627869939625101 7157739578485451227359413)
                  ·
                    refine ⟨671038085483011052564945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7157739578485451227359413 671038085483011052564945)
                    ·
                      rfl

theorem cell23_3920526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3920526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920526 prefixEnd_3920526 := by exact prefixLift 3920526
  have htrace : WordTrace (prefixWord ++ tailWord_3920526) baseStart_3920526 baseEnd_3920526 := by
    simpa [prefixWord, tailWord_3920526, baseEnd_3920526] using wordTrace_append hprefix tailTrace_3920526
  have hstable : (prefixWord ++ tailWord_3920526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920526).length < 2 ^ (prefixWord ++ tailWord_3920526).sum := by decide
  have hdescent : baseEnd_3920526 < baseStart_3920526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920530 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 6]
def baseStart_3920530 : Nat := 118140960795 + 3920530 * 2 ^ 59
def prefixEnd_3920530 : Nat := 4983230072969 + 3 ^ 40 * 3920530 * 2
def baseEnd_3920530 : Nat := 223679590041294571338313

theorem tailTrace_3920530 : CollatzResearch.WordTrace tailWord_3920530 prefixEnd_3920530 223679590041294571338313 := by
  unfold tailWord_3920530
  simp only [CollatzResearch.WordTrace]
  refine ⟨35748369121649214515415761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95328984324397905374442029 35748369121649214515415761)
  ·
    refine ⟨26811276841236910886561821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35748369121649214515415761 26811276841236910886561821)
    ·
      refine ⟨10054228815463841582460683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26811276841236910886561821 10054228815463841582460683)
      ·
        refine ⟨15081343223195762373691025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10054228815463841582460683 15081343223195762373691025)
        ·
          refine ⟨11311007417396821780268269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15081343223195762373691025 11311007417396821780268269)
          ·
            refine ⟨4241627781523808167600601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11311007417396821780268269 4241627781523808167600601)
            ·
              refine ⟨3181220836142856125700451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4241627781523808167600601 3181220836142856125700451)
              ·
                refine ⟨4771831254214284188550677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181220836142856125700451 4771831254214284188550677)
                ·
                  refine ⟨223679590041294571338313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4771831254214284188550677 223679590041294571338313)
                  ·
                    rfl

theorem cell23_3920530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_3920530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920530 prefixEnd_3920530 := by exact prefixLift 3920530
  have htrace : WordTrace (prefixWord ++ tailWord_3920530) baseStart_3920530 baseEnd_3920530 := by
    simpa [prefixWord, tailWord_3920530, baseEnd_3920530] using wordTrace_append hprefix tailTrace_3920530
  have hstable : (prefixWord ++ tailWord_3920530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920530).length < 2 ^ (prefixWord ++ tailWord_3920530).sum := by decide
  have hdescent : baseEnd_3920530 < baseStart_3920530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920573 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_3920573 : Nat := 118140960795 + 3920573 * 2 ^ 59
def prefixEnd_3920573 : Nat := 4983230072969 + 3 ^ 40 * 3920573 * 2
def baseEnd_3920573 : Nat := 671046130013264824602373

theorem tailTrace_3920573 : CollatzResearch.WordTrace tailWord_3920573 prefixEnd_3920573 671046130013264824602373 := by
  unfold tailWord_3920573
  simp only [CollatzResearch.WordTrace]
  refine ⟨142995044825441076405478373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95330029883627384270318915 142995044825441076405478373)
  ·
    refine ⟨26811570904770201826027195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142995044825441076405478373 26811570904770201826027195)
    ·
      refine ⟨40217356357155302739040793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26811570904770201826027195 40217356357155302739040793)
      ·
        refine ⟨30163017267866477054280595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40217356357155302739040793 30163017267866477054280595)
        ·
          refine ⟨45244525901799715581420893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30163017267866477054280595 45244525901799715581420893)
          ·
            refine ⟨16966697213174893343032835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45244525901799715581420893 16966697213174893343032835)
            ·
              refine ⟨25450045819762340014549253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16966697213174893343032835 25450045819762340014549253)
              ·
                refine ⟨4771883591205438752727985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25450045819762340014549253 4771883591205438752727985)
                ·
                  refine ⟨3578912693404079064545989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4771883591205438752727985 3578912693404079064545989)
                  ·
                    refine ⟨671046130013264824602373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3578912693404079064545989 671046130013264824602373)
                    ·
                      rfl

theorem cell23_3920573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_3920573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920573 prefixEnd_3920573 := by exact prefixLift 3920573
  have htrace : WordTrace (prefixWord ++ tailWord_3920573) baseStart_3920573 baseEnd_3920573 := by
    simpa [prefixWord, tailWord_3920573, baseEnd_3920573] using wordTrace_append hprefix tailTrace_3920573
  have hstable : (prefixWord ++ tailWord_3920573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920573).length < 2 ^ (prefixWord ++ tailWord_3920573).sum := by decide
  have hdescent : baseEnd_3920573 < baseStart_3920573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920586 : List Nat := [3, 1, 2, 1, 4, 1, 3, 8]
def baseStart_3920586 : Nat := 118140960795 + 3920586 * 2 ^ 59
def prefixEnd_3920586 : Nat := 4983230072969 + 3 ^ 40 * 3920586 * 2
def baseEnd_3920586 : Nat := 74560928344011219368317

theorem tailTrace_3920586 : CollatzResearch.WordTrace tailWord_3920586 prefixEnd_3920586 74560928344011219368317 := by
  unfold tailWord_3920586
  simp only [CollatzResearch.WordTrace]
  refine ⟨35748879743598494906425403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95330345982929319750467741 35748879743598494906425403)
  ·
    refine ⟨53623319615397742359638105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35748879743598494906425403 53623319615397742359638105)
    ·
      refine ⟨40217489711548306769728579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53623319615397742359638105 40217489711548306769728579)
      ·
        refine ⟨60326234567322460154592869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40217489711548306769728579 60326234567322460154592869)
        ·
          refine ⟨11311168981372961278986163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60326234567322460154592869 11311168981372961278986163)
          ·
            refine ⟨16966753472059441918479245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311168981372961278986163 16966753472059441918479245)
            ·
              refine ⟨6362532552022290719429717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16966753472059441918479245 6362532552022290719429717)
              ·
                refine ⟨74560928344011219368317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6362532552022290719429717 74560928344011219368317)
                ·
                  rfl

theorem cell23_3920586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 8].length) (baseStart_3920586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920586 prefixEnd_3920586 := by exact prefixLift 3920586
  have htrace : WordTrace (prefixWord ++ tailWord_3920586) baseStart_3920586 baseEnd_3920586 := by
    simpa [prefixWord, tailWord_3920586, baseEnd_3920586] using wordTrace_append hprefix tailTrace_3920586
  have hstable : (prefixWord ++ tailWord_3920586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920586).length < 2 ^ (prefixWord ++ tailWord_3920586).sum := by decide
  have hdescent : baseEnd_3920586 < baseStart_3920586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920613 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3920613 : Nat := 118140960795 + 3920613 * 2 ^ 59
def prefixEnd_3920613 : Nat := 4983230072969 + 3 ^ 40 * 3920613 * 2
def baseEnd_3920613 : Nat := 2013158929265974317306935

theorem tailTrace_3920613 : CollatzResearch.WordTrace tailWord_3920613 prefixEnd_3920613 2013158929265974317306935 := by
  unfold tailWord_3920613
  simp only [CollatzResearch.WordTrace]
  refine ⟨142996503745296163236934493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95331002496864108824622995 142996503745296163236934493)
  ·
    refine ⟨53623688904486061213850435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142996503745296163236934493 53623688904486061213850435)
    ·
      refine ⟨80435533356729091820775653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53623688904486061213850435 80435533356729091820775653)
      ·
        refine ⟨15081662504386704716395435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80435533356729091820775653 15081662504386704716395435)
        ·
          refine ⟨22622493756580057074593153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15081662504386704716395435 22622493756580057074593153)
          ·
            refine ⟨16966870317435042805944865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22622493756580057074593153 16966870317435042805944865)
            ·
              refine ⟨12725152738076282104458649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16966870317435042805944865 12725152738076282104458649)
              ·
                refine ⟨9543864553557211578343987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12725152738076282104458649 9543864553557211578343987)
                ·
                  refine ⟨14315796830335817367515981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9543864553557211578343987 14315796830335817367515981)
                  ·
                    refine ⟨5368423811375931512818493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14315796830335817367515981 5368423811375931512818493)
                    ·
                      refine ⟨2013158929265974317306935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5368423811375931512818493 2013158929265974317306935)
                      ·
                        rfl

theorem cell23_3920613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3920613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920613 prefixEnd_3920613 := by exact prefixLift 3920613
  have htrace : WordTrace (prefixWord ++ tailWord_3920613) baseStart_3920613 baseEnd_3920613 := by
    simpa [prefixWord, tailWord_3920613, baseEnd_3920613] using wordTrace_append hprefix tailTrace_3920613
  have hstable : (prefixWord ++ tailWord_3920613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920613).length < 2 ^ (prefixWord ++ tailWord_3920613).sum := by decide
  have hdescent : baseEnd_3920613 < baseStart_3920613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920630 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3920630 : Nat := 118140960795 + 3920630 * 2 ^ 59
def prefixEnd_3920630 : Nat := 4983230072969 + 3 ^ 40 * 3920630 * 2
def baseEnd_3920630 : Nat := 2013167658437100750794357

theorem tailTrace_3920630 : CollatzResearch.WordTrace tailWord_3920630 prefixEnd_3920630 2013167658437100750794357 := by
  unfold tailWord_3920630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937320236639660946268959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95331415857489716760202229 8937320236639660946268959)
  ·
    refine ⟨13405980354959491419403439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8937320236639660946268959 13405980354959491419403439)
    ·
      refine ⟨20108970532439237129105159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13405980354959491419403439 20108970532439237129105159)
      ·
        refine ⟨30163455798658855693657739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20108970532439237129105159 30163455798658855693657739)
        ·
          refine ⟨45245183697988283540486609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30163455798658855693657739 45245183697988283540486609)
          ·
            refine ⟨33933887773491212655364957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45245183697988283540486609 33933887773491212655364957)
            ·
              refine ⟨12725207915059204745761859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33933887773491212655364957 12725207915059204745761859)
              ·
                refine ⟨19087811872588807118642789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12725207915059204745761859 19087811872588807118642789)
                ·
                  refine ⟨3578964726110401334745523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19087811872588807118642789 3578964726110401334745523)
                  ·
                    refine ⟨5368447089165602002118285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3578964726110401334745523 5368447089165602002118285)
                    ·
                      refine ⟨2013167658437100750794357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5368447089165602002118285 2013167658437100750794357)
                      ·
                        rfl

theorem cell23_3920630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3920630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920630 prefixEnd_3920630 := by exact prefixLift 3920630
  have htrace : WordTrace (prefixWord ++ tailWord_3920630) baseStart_3920630 baseEnd_3920630 := by
    simpa [prefixWord, tailWord_3920630, baseEnd_3920630] using wordTrace_append hprefix tailTrace_3920630
  have hstable : (prefixWord ++ tailWord_3920630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920630).length < 2 ^ (prefixWord ++ tailWord_3920630).sum := by decide
  have hdescent : baseEnd_3920630 < baseStart_3920630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920693 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 7]
def baseStart_3920693 : Nat := 118140960795 + 3920693 * 2 ^ 59
def prefixEnd_3920693 : Nat := 4983230072969 + 3 ^ 40 * 3920693 * 2
def baseEnd_3920693 : Nat := 223688889746481556034063

theorem tailTrace_3920693 : CollatzResearch.WordTrace tailWord_3920693 prefixEnd_3920693 223688889746481556034063 := by
  unfold tailWord_3920693
  simp only [CollatzResearch.WordTrace]
  refine ⟨142999421585006336899846733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95332947723337557933231155 142999421585006336899846733)
  ·
    refine ⟨53624783094377376337442525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142999421585006336899846733 53624783094377376337442525)
    ·
      refine ⟨20109293660391516126540947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53624783094377376337442525 20109293660391516126540947)
      ·
        refine ⟨30163940490587274189811421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20109293660391516126540947 30163940490587274189811421)
        ·
          refine ⟨11311477683970227821179283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30163940490587274189811421 11311477683970227821179283)
          ·
            refine ⟨16967216525955341731768925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311477683970227821179283 16967216525955341731768925)
            ·
              refine ⟨6362706197233253149413347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16967216525955341731768925 6362706197233253149413347)
              ·
                refine ⟨9544059295849879724120021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362706197233253149413347 9544059295849879724120021)
                ·
                  refine ⟨223688889746481556034063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9544059295849879724120021 223688889746481556034063)
                  ·
                    rfl

theorem cell23_3920693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_3920693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920693 prefixEnd_3920693 := by exact prefixLift 3920693
  have htrace : WordTrace (prefixWord ++ tailWord_3920693) baseStart_3920693 baseEnd_3920693 := by
    simpa [prefixWord, tailWord_3920693, baseEnd_3920693] using wordTrace_append hprefix tailTrace_3920693
  have hstable : (prefixWord ++ tailWord_3920693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920693).length < 2 ^ (prefixWord ++ tailWord_3920693).sum := by decide
  have hdescent : baseEnd_3920693 < baseStart_3920693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920708 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3920708 : Nat := 118140960795 + 3920708 * 2 ^ 59
def prefixEnd_3920708 : Nat := 4983230072969 + 3 ^ 40 * 3920708 * 2
def baseEnd_3920708 : Nat := 2013207709928151445618999

theorem tailTrace_3920708 : CollatzResearch.WordTrace tailWord_3920708 prefixEnd_3920708 2013207709928151445618999 := by
  unfold tailWord_3920708
  simp only [CollatzResearch.WordTrace]
  refine ⟨71499984339975997230821389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95333312453301329641095185 71499984339975997230821389)
  ·
    refine ⟨26812494127490998961558021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71499984339975997230821389 26812494127490998961558021)
    ·
      refine ⟨5027342648904562305292129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26812494127490998961558021 5027342648904562305292129)
      ·
        refine ⟨3770506986678421728969097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5027342648904562305292129 3770506986678421728969097)
        ·
          refine ⟨2827880240008816296726823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770506986678421728969097 2827880240008816296726823)
          ·
            refine ⟨4241820360013224445090235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827880240008816296726823 4241820360013224445090235)
            ·
              refine ⟨6362730540019836667635353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4241820360013224445090235 6362730540019836667635353)
              ·
                refine ⟨4772047905014877500726515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362730540019836667635353 4772047905014877500726515)
                ·
                  refine ⟨7158071857522316251089773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772047905014877500726515 7158071857522316251089773)
                  ·
                    refine ⟨2684276946570868594158665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7158071857522316251089773 2684276946570868594158665)
                    ·
                      refine ⟨2013207709928151445618999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684276946570868594158665 2013207709928151445618999)
                      ·
                        rfl

theorem cell23_3920708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3920708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920708 prefixEnd_3920708 := by exact prefixLift 3920708
  have htrace : WordTrace (prefixWord ++ tailWord_3920708) baseStart_3920708 baseEnd_3920708 := by
    simpa [prefixWord, tailWord_3920708, baseEnd_3920708] using wordTrace_append hprefix tailTrace_3920708
  have hstable : (prefixWord ++ tailWord_3920708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920708).length < 2 ^ (prefixWord ++ tailWord_3920708).sum := by decide
  have hdescent : baseEnd_3920708 < baseStart_3920708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920763 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 3]
def baseStart_3920763 : Nat := 118140960795 + 3920763 * 2 ^ 59
def prefixEnd_3920763 : Nat := 4983230072969 + 3 ^ 40 * 3920763 * 2
def baseEnd_3920763 : Nat := 2013235951364148730431245

theorem tailTrace_3920763 : CollatzResearch.WordTrace tailWord_3920763 prefixEnd_3920763 2013235951364148730431245 := by
  unfold tailWord_3920763
  simp only [CollatzResearch.WordTrace]
  refine ⟨143001974694752738854894943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95334649796501825903263295 143001974694752738854894943)
  ·
    refine ⟨214502962042129108282342415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143001974694752738854894943 214502962042129108282342415)
    ·
      refine ⟨321754443063193662423513623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214502962042129108282342415 321754443063193662423513623)
      ·
        refine ⟨482631664594790493635270435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321754443063193662423513623 482631664594790493635270435)
        ·
          refine ⟨723947496892185740452905653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482631664594790493635270435 723947496892185740452905653)
          ·
            refine ⟨67870077833642413167459905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 723947496892185740452905653 67870077833642413167459905)
            ·
              refine ⟨50902558375231809875594929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67870077833642413167459905 50902558375231809875594929)
              ·
                refine ⟨38176918781423857406696197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50902558375231809875594929 38176918781423857406696197)
                ·
                  refine ⟨7158172271516973263755537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38176918781423857406696197 7158172271516973263755537)
                  ·
                    refine ⟨5368629203637729947816653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158172271516973263755537 5368629203637729947816653)
                    ·
                      refine ⟨2013235951364148730431245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5368629203637729947816653 2013235951364148730431245)
                      ·
                        rfl

theorem cell23_3920763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 3].length) (baseStart_3920763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920763 prefixEnd_3920763 := by exact prefixLift 3920763
  have htrace : WordTrace (prefixWord ++ tailWord_3920763) baseStart_3920763 baseEnd_3920763 := by
    simpa [prefixWord, tailWord_3920763, baseEnd_3920763] using wordTrace_append hprefix tailTrace_3920763
  have hstable : (prefixWord ++ tailWord_3920763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920763).length < 2 ^ (prefixWord ++ tailWord_3920763).sum := by decide
  have hdescent : baseEnd_3920763 < baseStart_3920763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920780 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 2, 2, 3]
def baseStart_3920780 : Nat := 118140960795 + 3920780 * 2 ^ 59
def prefixEnd_3920780 : Nat := 4983230072969 + 3 ^ 40 * 3920780 * 2
def baseEnd_3920780 : Nat := 2013244680535275163918667

theorem tailTrace_3920780 : CollatzResearch.WordTrace tailWord_3920780 prefixEnd_3920780 2013244680535275163918667 := by
  unfold tailWord_3920780
  simp only [CollatzResearch.WordTrace]
  refine ⟨71501297367845575379131897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95335063157127433838842529 71501297367845575379131897)
  ·
    refine ⟨53625973025884181534348923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71501297367845575379131897 53625973025884181534348923)
    ·
      refine ⟨80438959538826272301523385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53625973025884181534348923 80438959538826272301523385)
      ·
        refine ⟨60329219654119704226142539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80438959538826272301523385 60329219654119704226142539)
        ·
          refine ⟨90493829481179556339213809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60329219654119704226142539 90493829481179556339213809)
          ·
            refine ⟨67870372110884667254410357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90493829481179556339213809 67870372110884667254410357)
            ·
              refine ⟨6362847385395437555100971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67870372110884667254410357 6362847385395437555100971)
              ·
                refine ⟨9544271078093156332651457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362847385395437555100971 9544271078093156332651457)
                ·
                  refine ⟨7158203308569867249488593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9544271078093156332651457 7158203308569867249488593)
                  ·
                    refine ⟨5368652481427400437116445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158203308569867249488593 5368652481427400437116445)
                    ·
                      refine ⟨2013244680535275163918667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5368652481427400437116445 2013244680535275163918667)
                      ·
                        rfl

theorem cell23_3920780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_3920780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920780 prefixEnd_3920780 := by exact prefixLift 3920780
  have htrace : WordTrace (prefixWord ++ tailWord_3920780) baseStart_3920780 baseEnd_3920780 := by
    simpa [prefixWord, tailWord_3920780, baseEnd_3920780] using wordTrace_append hprefix tailTrace_3920780
  have hstable : (prefixWord ++ tailWord_3920780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920780).length < 2 ^ (prefixWord ++ tailWord_3920780).sum := by decide
  have hdescent : baseEnd_3920780 < baseStart_3920780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920817 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 6]
def baseStart_3920817 : Nat := 118140960795 + 3920817 * 2 ^ 59
def prefixEnd_3920817 : Nat := 4983230072969 + 3 ^ 40 * 3920817 * 2
def baseEnd_3920817 : Nat := 223695964368832391017333

theorem tailTrace_3920817 : CollatzResearch.WordTrace tailWord_3920817 prefixEnd_3920817 223695964368832391017333 := by
  unfold tailWord_3920817
  simp only [CollatzResearch.WordTrace]
  refine ⟨143003944236557106077360705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95335962824371404051573803 143003944236557106077360705)
  ·
    refine ⟨107252958177417829558020529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143003944236557106077360705 107252958177417829558020529)
    ·
      refine ⟨80439718633063372168515397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107252958177417829558020529 80439718633063372168515397)
      ·
        refine ⟨15082447243699382281596637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80439718633063372168515397 15082447243699382281596637)
        ·
          refine ⟨5655917716387268355598739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15082447243699382281596637 5655917716387268355598739)
          ·
            refine ⟨8483876574580902533398109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655917716387268355598739 8483876574580902533398109)
            ·
              refine ⟨3181453715467838450024291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8483876574580902533398109 3181453715467838450024291)
              ·
                refine ⟨4772180573201757675036437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181453715467838450024291 4772180573201757675036437)
                ·
                  refine ⟨223695964368832391017333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4772180573201757675036437 223695964368832391017333)
                  ·
                    rfl

theorem cell23_3920817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 6].length) (baseStart_3920817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920817 prefixEnd_3920817 := by exact prefixLift 3920817
  have htrace : WordTrace (prefixWord ++ tailWord_3920817) baseStart_3920817 baseEnd_3920817 := by
    simpa [prefixWord, tailWord_3920817, baseEnd_3920817] using wordTrace_append hprefix tailTrace_3920817
  have hstable : (prefixWord ++ tailWord_3920817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920817).length < 2 ^ (prefixWord ++ tailWord_3920817).sum := by decide
  have hdescent : baseEnd_3920817 < baseStart_3920817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920854 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_3920854 : Nat := 118140960795 + 3920854 * 2 ^ 59
def prefixEnd_3920854 : Nat := 4983230072969 + 3 ^ 40 * 3920854 * 2
def baseEnd_3920854 : Nat := 2013282678103707874393327

theorem tailTrace_3920854 : CollatzResearch.WordTrace tailWord_3920854 prefixEnd_3920854 2013282678103707874393327 := by
  unfold tailWord_3920854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8937830858588941337278601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95336862491615374264305077 8937830858588941337278601)
  ·
    refine ⟨6703373143941706002958951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8937830858588941337278601 6703373143941706002958951)
    ·
      refine ⟨10055059715912559004438427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703373143941706002958951 10055059715912559004438427)
      ·
        refine ⟨15082589573868838506657641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055059715912559004438427 15082589573868838506657641)
        ·
          refine ⟨11311942180401628879993231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15082589573868838506657641 11311942180401628879993231)
          ·
            refine ⟨16967913270602443319989847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311942180401628879993231 16967913270602443319989847)
            ·
              refine ⟨25451869905903664979984771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16967913270602443319989847 25451869905903664979984771)
              ·
                refine ⟨38177804858855497469977157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25451869905903664979984771 38177804858855497469977157)
                ·
                  refine ⟨7158338411035405775620717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38177804858855497469977157 7158338411035405775620717)
                  ·
                    refine ⟨2684376904138277165857769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7158338411035405775620717 2684376904138277165857769)
                    ·
                      refine ⟨2013282678103707874393327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684376904138277165857769 2013282678103707874393327)
                      ·
                        rfl

theorem cell23_3920854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_3920854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920854 prefixEnd_3920854 := by exact prefixLift 3920854
  have htrace : WordTrace (prefixWord ++ tailWord_3920854) baseStart_3920854 baseEnd_3920854 := by
    simpa [prefixWord, tailWord_3920854, baseEnd_3920854] using wordTrace_append hprefix tailTrace_3920854
  have hstable : (prefixWord ++ tailWord_3920854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920854).length < 2 ^ (prefixWord ++ tailWord_3920854).sum := by decide
  have hdescent : baseEnd_3920854 < baseStart_3920854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920904 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_3920904 : Nat := 118140960795 + 3920904 * 2 ^ 59
def prefixEnd_3920904 : Nat := 4983230072969 + 3 ^ 40 * 3920904 * 2
def baseEnd_3920904 : Nat := 2013308352136432678768097

theorem tailTrace_3920904 : CollatzResearch.WordTrace tailWord_3920904 prefixEnd_3920904 2013308352136432678768097 := by
  unfold tailWord_3920904
  simp only [CollatzResearch.WordTrace]
  refine ⟨71503558693620959967888883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95338078258161279957185177 71503558693620959967888883)
  ·
    refine ⟨107255338040431439951833325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71503558693620959967888883 107255338040431439951833325)
    ·
      refine ⟨40220751765161789981937497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107255338040431439951833325 40220751765161789981937497)
      ·
        refine ⟨30165563823871342486453123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40220751765161789981937497 30165563823871342486453123)
        ·
          refine ⟨45248345735807013729679685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30165563823871342486453123 45248345735807013729679685)
          ·
            refine ⟨8484064825463815074314941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45248345735807013729679685 8484064825463815074314941)
            ·
              refine ⟨3181524309548930652868103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8484064825463815074314941 3181524309548930652868103)
              ·
                refine ⟨4772286464323395979302155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181524309548930652868103 4772286464323395979302155)
                ·
                  refine ⟨7158429696485093968953233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772286464323395979302155 7158429696485093968953233)
                  ·
                    refine ⟨5368822272363820476714925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158429696485093968953233 5368822272363820476714925)
                    ·
                      refine ⟨2013308352136432678768097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5368822272363820476714925 2013308352136432678768097)
                      ·
                        rfl

theorem cell23_3920904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_3920904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920904 prefixEnd_3920904 := by exact prefixLift 3920904
  have htrace : WordTrace (prefixWord ++ tailWord_3920904) baseStart_3920904 baseEnd_3920904 := by
    simpa [prefixWord, tailWord_3920904, baseEnd_3920904] using wordTrace_append hprefix tailTrace_3920904
  have hstable : (prefixWord ++ tailWord_3920904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920904).length < 2 ^ (prefixWord ++ tailWord_3920904).sum := by decide
  have hdescent : baseEnd_3920904 < baseStart_3920904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920913 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_3920913 : Nat := 118140960795 + 3920913 * 2 ^ 59
def prefixEnd_3920913 : Nat := 4983230072969 + 3 ^ 40 * 3920913 * 2
def baseEnd_3920913 : Nat := 2013312973462323143555555

theorem tailTrace_3920913 : CollatzResearch.WordTrace tailWord_3920913 prefixEnd_3920913 2013312973462323143555555 := by
  unfold tailWord_3920913
  simp only [CollatzResearch.WordTrace]
  refine ⟨143007445644209314472855393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95338297096139542981903595 143007445644209314472855393)
  ·
    refine ⟨107255584233156985854641545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143007445644209314472855393 107255584233156985854641545)
    ·
      refine ⟨80441688174867739390981159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107255584233156985854641545 80441688174867739390981159)
      ·
        refine ⟨120662532262301609086471739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80441688174867739390981159 120662532262301609086471739)
        ·
          refine ⟨180993798393452413629707609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120662532262301609086471739 180993798393452413629707609)
          ·
            refine ⟨135745348795089310222280707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180993798393452413629707609 135745348795089310222280707)
            ·
              refine ⟨203618023192633965333421061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135745348795089310222280707 203618023192633965333421061)
              ·
                refine ⟨38178379348618868500016449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203618023192633965333421061 38178379348618868500016449)
                ·
                  refine ⟨28633784511464151375012337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38178379348618868500016449 28633784511464151375012337)
                  ·
                    refine ⟨21475338383598113531259253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28633784511464151375012337 21475338383598113531259253)
                    ·
                      refine ⟨2013312973462323143555555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21475338383598113531259253 2013312973462323143555555)
                      ·
                        rfl

theorem cell23_3920913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_3920913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920913 prefixEnd_3920913 := by exact prefixLift 3920913
  have htrace : WordTrace (prefixWord ++ tailWord_3920913) baseStart_3920913 baseEnd_3920913 := by
    simpa [prefixWord, tailWord_3920913, baseEnd_3920913] using wordTrace_append hprefix tailTrace_3920913
  have hstable : (prefixWord ++ tailWord_3920913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920913).length < 2 ^ (prefixWord ++ tailWord_3920913).sum := by decide
  have hdescent : baseEnd_3920913 < baseStart_3920913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920927 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 3, 3, 2]
def baseStart_3920927 : Nat := 118140960795 + 3920927 * 2 ^ 59
def prefixEnd_3920927 : Nat := 4983230072969 + 3 ^ 40 * 3920927 * 2
def baseEnd_3920927 : Nat := 2013320162191486088780491

theorem tailTrace_3920927 : CollatzResearch.WordTrace tailWord_3920927 prefixEnd_3920927 2013320162191486088780491 := by
  unfold tailWord_3920927
  simp only [CollatzResearch.WordTrace]
  refine ⟨143007956266158594863865035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95338637510772396575910023 143007956266158594863865035)
  ·
    refine ⟨214511934399237892295797553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143007956266158594863865035 214511934399237892295797553)
    ·
      refine ⟨160883950799428419221848165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214511934399237892295797553 160883950799428419221848165)
      ·
        refine ⟨30165740774892828604096531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160883950799428419221848165 30165740774892828604096531)
        ·
          refine ⟨45248611162339242906144797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30165740774892828604096531 45248611162339242906144797)
          ·
            refine ⟨16968229185877216089804299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45248611162339242906144797 16968229185877216089804299)
            ·
              refine ⟨25452343778815824134706449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16968229185877216089804299 25452343778815824134706449)
              ·
                refine ⟨19089257834111868101029837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25452343778815824134706449 19089257834111868101029837)
                ·
                  refine ⟨7158471687791950537886189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19089257834111868101029837 7158471687791950537886189)
                  ·
                    refine ⟨2684426882921981451707321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7158471687791950537886189 2684426882921981451707321)
                    ·
                      refine ⟨2013320162191486088780491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684426882921981451707321 2013320162191486088780491)
                      ·
                        rfl

theorem cell23_3920927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_3920927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920927 prefixEnd_3920927 := by exact prefixLift 3920927
  have htrace : WordTrace (prefixWord ++ tailWord_3920927) baseStart_3920927 baseEnd_3920927 := by
    simpa [prefixWord, tailWord_3920927, baseEnd_3920927] using wordTrace_append hprefix tailTrace_3920927
  have hstable : (prefixWord ++ tailWord_3920927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920927).length < 2 ^ (prefixWord ++ tailWord_3920927).sum := by decide
  have hdescent : baseEnd_3920927 < baseStart_3920927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920961 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_3920961 : Nat := 118140960795 + 3920961 * 2 ^ 59
def prefixEnd_3920961 : Nat := 4983230072969 + 3 ^ 40 * 3920961 * 2
def baseEnd_3920961 : Nat := 2013337620533738955755335

theorem tailTrace_3920961 : CollatzResearch.WordTrace tailWord_3920961 prefixEnd_3920961 2013337620533738955755335 := by
  unfold tailWord_3920961
  simp only [CollatzResearch.WordTrace]
  refine ⟨143009196348035418670602737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95339464232023612447068491 143009196348035418670602737)
  ·
    refine ⟨107256897261026564002952053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143009196348035418670602737 107256897261026564002952053)
    ·
      refine ⟨10055334118221240375276755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107256897261026564002952053 10055334118221240375276755)
      ·
        refine ⟨15083001177331860562915133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055334118221240375276755 15083001177331860562915133)
        ·
          refine ⟨5656125441499447711093175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15083001177331860562915133 5656125441499447711093175)
          ·
            refine ⟨8484188162249171566639763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656125441499447711093175 8484188162249171566639763)
            ·
              refine ⟨12726282243373757349959645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8484188162249171566639763 12726282243373757349959645)
              ·
                refine ⟨4772355841265159006234867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12726282243373757349959645 4772355841265159006234867)
                ·
                  refine ⟨7158533761897738509352301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772355841265159006234867 7158533761897738509352301)
                  ·
                    refine ⟨2684450160711651941007113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7158533761897738509352301 2684450160711651941007113)
                    ·
                      refine ⟨2013337620533738955755335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684450160711651941007113 2013337620533738955755335)
                      ·
                        rfl

theorem cell23_3920961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_3920961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920961 prefixEnd_3920961 := by exact prefixLift 3920961
  have htrace : WordTrace (prefixWord ++ tailWord_3920961) baseStart_3920961 baseEnd_3920961 := by
    simpa [prefixWord, tailWord_3920961, baseEnd_3920961] using wordTrace_append hprefix tailTrace_3920961
  have hstable : (prefixWord ++ tailWord_3920961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920961).length < 2 ^ (prefixWord ++ tailWord_3920961).sum := by decide
  have hdescent : baseEnd_3920961 < baseStart_3920961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920963 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 9]
def baseStart_3920963 : Nat := 118140960795 + 3920963 * 2 ^ 59
def prefixEnd_3920963 : Nat := 4983230072969 + 3 ^ 40 * 3920963 * 2
def baseEnd_3920963 : Nat := 223704294166116438658925

theorem tailTrace_3920963 : CollatzResearch.WordTrace tailWord_3920963 prefixEnd_3920963 223704294166116438658925 := by
  unfold tailWord_3920963
  simp only [CollatzResearch.WordTrace]
  refine ⟨143009269294028173012175543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95339512862685448674783695 143009269294028173012175543)
  ·
    refine ⟨214513903941042259518263315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143009269294028173012175543 214513903941042259518263315)
    ·
      refine ⟨321770855911563389277394973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214513903941042259518263315 321770855911563389277394973)
      ·
        refine ⟨120664070966836270979023115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321770855911563389277394973 120664070966836270979023115)
        ·
          refine ⟨180996106450254406468534673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120664070966836270979023115 180996106450254406468534673)
          ·
            refine ⟨135747079837690804851401005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180996106450254406468534673 135747079837690804851401005)
            ·
              refine ⟨50905154939134051819275377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135747079837690804851401005 50905154939134051819275377)
              ·
                refine ⟨38178866204350538864456533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50905154939134051819275377 38178866204350538864456533)
                ·
                  refine ⟨223704294166116438658925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38178866204350538864456533 223704294166116438658925)
                  ·
                    rfl

theorem cell23_3920963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 9].length) (baseStart_3920963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920963 prefixEnd_3920963 := by exact prefixLift 3920963
  have htrace : WordTrace (prefixWord ++ tailWord_3920963) baseStart_3920963 baseEnd_3920963 := by
    simpa [prefixWord, tailWord_3920963, baseEnd_3920963] using wordTrace_append hprefix tailTrace_3920963
  have hstable : (prefixWord ++ tailWord_3920963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920963).length < 2 ^ (prefixWord ++ tailWord_3920963).sum := by decide
  have hdescent : baseEnd_3920963 < baseStart_3920963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920970 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_3920970 : Nat := 118140960795 + 3920970 * 2 ^ 59
def prefixEnd_3920970 : Nat := 4983230072969 + 3 ^ 40 * 3920970 * 2
def baseEnd_3920970 : Nat := 2013342241859629420542793

theorem tailTrace_3920970 : CollatzResearch.WordTrace tailWord_3920970 prefixEnd_3920970 2013342241859629420542793 := by
  unfold tailWord_3920970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752381151250703301920091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95339683070001875471786909 35752381151250703301920091)
  ·
    refine ⟨53628571726876054952880137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35752381151250703301920091 53628571726876054952880137)
    ·
      refine ⟨40221428795157041214660103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53628571726876054952880137 40221428795157041214660103)
      ·
        refine ⟨60332143192735561821990155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40221428795157041214660103 60332143192735561821990155)
        ·
          refine ⟨90498214789103342732985233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60332143192735561821990155 90498214789103342732985233)
          ·
            refine ⟨67873661091827507049738925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90498214789103342732985233 67873661091827507049738925)
            ·
              refine ⟨25452622909435315143652097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67873661091827507049738925 25452622909435315143652097)
              ·
                refine ⟨19089467182076486357739073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25452622909435315143652097 19089467182076486357739073)
                ·
                  refine ⟨14317100386557364768304305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19089467182076486357739073 14317100386557364768304305)
                  ·
                    refine ⟨10737825289918023576228229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14317100386557364768304305 10737825289918023576228229)
                    ·
                      refine ⟨2013342241859629420542793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10737825289918023576228229 2013342241859629420542793)
                      ·
                        rfl

theorem cell23_3920970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_3920970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920970 prefixEnd_3920970 := by exact prefixLift 3920970
  have htrace : WordTrace (prefixWord ++ tailWord_3920970) baseStart_3920970 baseEnd_3920970 := by
    simpa [prefixWord, tailWord_3920970, baseEnd_3920970] using wordTrace_append hprefix tailTrace_3920970
  have hstable : (prefixWord ++ tailWord_3920970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920970).length < 2 ^ (prefixWord ++ tailWord_3920970).sum := by decide
  have hdescent : baseEnd_3920970 < baseStart_3920970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920974 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_3920974 : Nat := 118140960795 + 3920974 * 2 ^ 59
def prefixEnd_3920974 : Nat := 4983230072969 + 3 ^ 40 * 3920974 * 2
def baseEnd_3920974 : Nat := 2013344295782247404892775

theorem tailTrace_3920974 : CollatzResearch.WordTrace tailWord_3920974 prefixEnd_3920974 2013344295782247404892775 := by
  unfold tailWord_3920974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17876208812123540236353247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95339780331325547927217317 17876208812123540236353247)
  ·
    refine ⟨26814313218185310354529871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17876208812123540236353247 26814313218185310354529871)
    ·
      refine ⟨40221469827277965531794807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26814313218185310354529871 40221469827277965531794807)
      ·
        refine ⟨60332204740916948297692211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40221469827277965531794807 60332204740916948297692211)
        ·
          refine ⟨90498307111375422446538317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60332204740916948297692211 90498307111375422446538317)
          ·
            refine ⟨33936865166765783417451869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90498307111375422446538317 33936865166765783417451869)
            ·
              refine ⟨12726324437537168781544451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33936865166765783417451869 12726324437537168781544451)
              ·
                refine ⟨19089486656305753172316677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12726324437537168781544451 19089486656305753172316677)
                ·
                  refine ⟨3579278748057328719809377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19089486656305753172316677 3579278748057328719809377)
                  ·
                    refine ⟨2684459061042996539857033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3579278748057328719809377 2684459061042996539857033)
                    ·
                      refine ⟨2013344295782247404892775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684459061042996539857033 2013344295782247404892775)
                      ·
                        rfl

theorem cell23_3920974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_3920974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920974 prefixEnd_3920974 := by exact prefixLift 3920974
  have htrace : WordTrace (prefixWord ++ tailWord_3920974) baseStart_3920974 baseEnd_3920974 := by
    simpa [prefixWord, tailWord_3920974, baseEnd_3920974] using wordTrace_append hprefix tailTrace_3920974
  have hstable : (prefixWord ++ tailWord_3920974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920974).length < 2 ^ (prefixWord ++ tailWord_3920974).sum := by decide
  have hdescent : baseEnd_3920974 < baseStart_3920974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920980 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 7]
def baseStart_3920980 : Nat := 118140960795 + 3920980 * 2 ^ 59
def prefixEnd_3920980 : Nat := 4983230072969 + 3 ^ 40 * 3920980 * 2
def baseEnd_3920980 : Nat := 223705264074019375713083

theorem tailTrace_3920980 : CollatzResearch.WordTrace tailWord_3920980 prefixEnd_3920980 223705264074019375713083 := by
  unfold tailWord_3920980
  simp only [CollatzResearch.WordTrace]
  refine ⟨71504944667483292457772197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95339926223311056610362929 71504944667483292457772197)
  ·
    refine ⟨13407177125153117335832287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71504944667483292457772197 13407177125153117335832287)
    ·
      refine ⟨20110765687729676003748431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13407177125153117335832287 20110765687729676003748431)
      ·
        refine ⟨30166148531594514005622647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20110765687729676003748431 30166148531594514005622647)
        ·
          refine ⟨45249222797391771008433971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30166148531594514005622647 45249222797391771008433971)
          ·
            refine ⟨67873834196087656512650957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45249222797391771008433971 67873834196087656512650957)
            ·
              refine ⟨25452687823532871192244109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67873834196087656512650957 25452687823532871192244109)
              ·
                refine ⟨9544757933824826697091541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25452687823532871192244109 9544757933824826697091541)
                ·
                  refine ⟨223705264074019375713083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9544757933824826697091541 223705264074019375713083)
                  ·
                    rfl

theorem cell23_3920980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_3920980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920980 prefixEnd_3920980 := by exact prefixLift 3920980
  have htrace : WordTrace (prefixWord ++ tailWord_3920980) baseStart_3920980 baseEnd_3920980 := by
    simpa [prefixWord, tailWord_3920980, baseEnd_3920980] using wordTrace_append hprefix tailTrace_3920980
  have hstable : (prefixWord ++ tailWord_3920980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920980).length < 2 ^ (prefixWord ++ tailWord_3920980).sum := by decide
  have hdescent : baseEnd_3920980 < baseStart_3920980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3920991 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 2, 2, 2]
def baseStart_3920991 : Nat := 118140960795 + 3920991 * 2 ^ 59
def prefixEnd_3920991 : Nat := 4983230072969 + 3 ^ 40 * 3920991 * 2
def baseEnd_3920991 : Nat := 2013353024953373838380197

theorem tailTrace_3920991 : CollatzResearch.WordTrace tailWord_3920991 prefixEnd_3920991 2013353024953373838380197 := by
  unfold tailWord_3920991
  simp only [CollatzResearch.WordTrace]
  refine ⟨143010290537926733794194827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95340193691951155862796551 143010290537926733794194827)
  ·
    refine ⟨214515435806890100691292241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143010290537926733794194827 214515435806890100691292241)
    ·
      refine ⟨160886576855167575518469181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214515435806890100691292241 160886576855167575518469181)
      ·
        refine ⟨60332466320687840819425943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160886576855167575518469181 60332466320687840819425943)
        ·
          refine ⟨90498699481031761229138915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60332466320687840819425943 90498699481031761229138915)
          ·
            refine ⟨135748049221547641843708373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90498699481031761229138915 135748049221547641843708373)
            ·
              refine ⟨3181594903630022855711915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135748049221547641843708373 3181594903630022855711915)
              ·
                refine ⟨4772392355445034283567873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181594903630022855711915 4772392355445034283567873)
                ·
                  refine ⟨3579294266583775712675905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4772392355445034283567873 3579294266583775712675905)
                  ·
                    refine ⟨2684470699937831784506929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3579294266583775712675905 2684470699937831784506929)
                    ·
                      refine ⟨2013353024953373838380197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684470699937831784506929 2013353024953373838380197)
                      ·
                        rfl

theorem cell23_3920991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_3920991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3920991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3920991 prefixEnd_3920991 := by exact prefixLift 3920991
  have htrace : WordTrace (prefixWord ++ tailWord_3920991) baseStart_3920991 baseEnd_3920991 := by
    simpa [prefixWord, tailWord_3920991, baseEnd_3920991] using wordTrace_append hprefix tailTrace_3920991
  have hstable : (prefixWord ++ tailWord_3920991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3920991).length < 2 ^ (prefixWord ++ tailWord_3920991).sum := by decide
  have hdescent : baseEnd_3920991 < baseStart_3920991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3920991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921010 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_3921010 : Nat := 118140960795 + 3921010 * 2 ^ 59
def prefixEnd_3921010 : Nat := 4983230072969 + 3 ^ 40 * 3921010 * 2
def baseEnd_3921010 : Nat := 671120927028603088014203

theorem tailTrace_3921010 : CollatzResearch.WordTrace tailWord_3921010 prefixEnd_3921010 671120927028603088014203 := by
  unfold tailWord_3921010
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752745881214475009784121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95340655683238600026090989 35752745881214475009784121)
  ·
    refine ⟨26814559410910856257338091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35752745881214475009784121 26814559410910856257338091)
    ·
      refine ⟨40221839116366284386007137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26814559410910856257338091 40221839116366284386007137)
      ·
        refine ⟨30166379337274713289505353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40221839116366284386007137 30166379337274713289505353)
        ·
          refine ⟨22624784502956034967129015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30166379337274713289505353 22624784502956034967129015)
          ·
            refine ⟨33937176754434052450693523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22624784502956034967129015 33937176754434052450693523)
            ·
              refine ⟨50905765131651078676040285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33937176754434052450693523 50905765131651078676040285)
              ·
                refine ⟨19089661924369154503515107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50905765131651078676040285 19089661924369154503515107)
                ·
                  refine ⟨28634492886553731755272661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19089661924369154503515107 28634492886553731755272661)
                  ·
                    refine ⟨671120927028603088014203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28634492886553731755272661 671120927028603088014203)
                    ·
                      rfl

theorem cell23_3921010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_3921010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921010 prefixEnd_3921010 := by exact prefixLift 3921010
  have htrace : WordTrace (prefixWord ++ tailWord_3921010) baseStart_3921010 baseEnd_3921010 := by
    simpa [prefixWord, tailWord_3921010, baseEnd_3921010] using wordTrace_append hprefix tailTrace_3921010
  have hstable : (prefixWord ++ tailWord_3921010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921010).length < 2 ^ (prefixWord ++ tailWord_3921010).sum := by decide
  have hdescent : baseEnd_3921010 < baseStart_3921010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921020 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_3921020 : Nat := 118140960795 + 3921020 * 2 ^ 59
def prefixEnd_3921020 : Nat := 4983230072969 + 3 ^ 40 * 3921020 * 2
def baseEnd_3921020 : Nat := 2013367915892354224917563

theorem tailTrace_3921020 : CollatzResearch.WordTrace tailWord_3921020 prefixEnd_3921020 2013367915892354224917563 := by
  unfold tailWord_3921020
  simp only [CollatzResearch.WordTrace]
  refine ⟨71505674127410835873500257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95340898836547781164667009 71505674127410835873500257)
  ·
    refine ⟨53629255595558126905125193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71505674127410835873500257 53629255595558126905125193)
    ·
      refine ⟨40221941696668595178843895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53629255595558126905125193 40221941696668595178843895)
      ·
        refine ⟨60332912545002892768265843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40221941696668595178843895 60332912545002892768265843)
        ·
          refine ⟨90499368817504339152398765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60332912545002892768265843 90499368817504339152398765)
          ·
            refine ⟨33937263306564127182149537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90499368817504339152398765 33937263306564127182149537)
            ·
              refine ⟨25452947479923095386612153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33937263306564127182149537 25452947479923095386612153)
              ·
                refine ⟨19089710609942321539959115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25452947479923095386612153 19089710609942321539959115)
                ·
                  refine ⟨28634565914913482309938673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19089710609942321539959115 28634565914913482309938673)
                  ·
                    refine ⟨21475924436185111732454005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28634565914913482309938673 21475924436185111732454005)
                    ·
                      refine ⟨2013367915892354224917563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21475924436185111732454005 2013367915892354224917563)
                      ·
                        rfl

theorem cell23_3921020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_3921020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921020 prefixEnd_3921020 := by exact prefixLift 3921020
  have htrace : WordTrace (prefixWord ++ tailWord_3921020) baseStart_3921020 baseEnd_3921020 := by
    simpa [prefixWord, tailWord_3921020, baseEnd_3921020] using wordTrace_append hprefix tailTrace_3921020
  have hstable : (prefixWord ++ tailWord_3921020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921020).length < 2 ^ (prefixWord ++ tailWord_3921020).sum := by decide
  have hdescent : baseEnd_3921020 < baseStart_3921020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921057 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 5, 4]
def baseStart_3921057 : Nat := 118140960795 + 3921057 * 2 ^ 59
def prefixEnd_3921057 : Nat := 4983230072969 + 3 ^ 40 * 3921057 * 2
def baseEnd_3921057 : Nat := 671128971558856860051631

theorem tailTrace_3921057 : CollatzResearch.WordTrace tailWord_3921057 prefixEnd_3921057 671128971558856860051631 := by
  unfold tailWord_3921057
  simp only [CollatzResearch.WordTrace]
  refine ⟨143012697755687627066097425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95341798503791751377398283 143012697755687627066097425)
  ·
    refine ⟨107259523316765720299573069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143012697755687627066097425 107259523316765720299573069)
    ·
      refine ⟨40222321243787145112339901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107259523316765720299573069 40222321243787145112339901)
      ·
        refine ⟨15083370466420179417127463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40222321243787145112339901 15083370466420179417127463)
        ·
          refine ⟨22625055699630269125691195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15083370466420179417127463 22625055699630269125691195)
          ·
            refine ⟨33937583549445403688536793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22625055699630269125691195 33937583549445403688536793)
            ·
              refine ⟨25453187662084052766402595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33937583549445403688536793 25453187662084052766402595)
              ·
                refine ⟨38179781493126079149603893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25453187662084052766402595 38179781493126079149603893)
                ·
                  refine ⟨3579354514980569920275365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38179781493126079149603893 3579354514980569920275365)
                  ·
                    refine ⟨671128971558856860051631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3579354514980569920275365 671128971558856860051631)
                    ·
                      rfl

theorem cell23_3921057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_3921057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921057 prefixEnd_3921057 := by exact prefixLift 3921057
  have htrace : WordTrace (prefixWord ++ tailWord_3921057) baseStart_3921057 baseEnd_3921057 := by
    simpa [prefixWord, tailWord_3921057, baseEnd_3921057] using wordTrace_append hprefix tailTrace_3921057
  have hstable : (prefixWord ++ tailWord_3921057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921057).length < 2 ^ (prefixWord ++ tailWord_3921057).sum := by decide
  have hdescent : baseEnd_3921057 < baseStart_3921057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921084 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3921084 : Nat := 118140960795 + 3921084 * 2 ^ 59
def prefixEnd_3921084 : Nat := 4983230072969 + 3 ^ 40 * 3921084 * 2
def baseEnd_3921084 : Nat := 2013400778654241974517269

theorem tailTrace_3921084 : CollatzResearch.WordTrace tailWord_3921084 prefixEnd_3921084 2013400778654241974517269 := by
  unfold tailWord_3921084
  simp only [CollatzResearch.WordTrace]
  refine ⟨71506841263294905338665153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95342455017726540451553537 71506841263294905338665153)
  ·
    refine ⟨53630130947471179003998865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71506841263294905338665153 53630130947471179003998865)
    ·
      refine ⟨40222598210603384252999149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53630130947471179003998865 40222598210603384252999149)
      ·
        refine ⟨15083474328976269094874681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40222598210603384252999149 15083474328976269094874681)
        ·
          refine ⟨11312605746732201821156011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15083474328976269094874681 11312605746732201821156011)
          ·
            refine ⟨16968908620098302731734017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11312605746732201821156011 16968908620098302731734017)
            ·
              refine ⟨12726681465073727048800513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16968908620098302731734017 12726681465073727048800513)
              ·
                refine ⟨9545011098805295286600385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12726681465073727048800513 9545011098805295286600385)
                ·
                  refine ⟨7158758324103971464950289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9545011098805295286600385 7158758324103971464950289)
                  ·
                    refine ⟨5369068743077978598712717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158758324103971464950289 5369068743077978598712717)
                    ·
                      refine ⟨2013400778654241974517269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5369068743077978598712717 2013400778654241974517269)
                      ·
                        rfl

theorem cell23_3921084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3921084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921084 prefixEnd_3921084 := by exact prefixLift 3921084
  have htrace : WordTrace (prefixWord ++ tailWord_3921084) baseStart_3921084 baseEnd_3921084 := by
    simpa [prefixWord, tailWord_3921084, baseEnd_3921084] using wordTrace_append hprefix tailTrace_3921084
  have hstable : (prefixWord ++ tailWord_3921084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921084).length < 2 ^ (prefixWord ++ tailWord_3921084).sum := by decide
  have hdescent : baseEnd_3921084 < baseStart_3921084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921107 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 3, 5, 2]
def baseStart_3921107 : Nat := 118140960795 + 3921107 * 2 ^ 59
def prefixEnd_3921107 : Nat := 4983230072969 + 3 ^ 40 * 3921107 * 2
def baseEnd_3921107 : Nat := 2013412588709295384529663

theorem tailTrace_3921107 : CollatzResearch.WordTrace tailWord_3921107 prefixEnd_3921107 2013412588709295384529663 := by
  unfold tailWord_3921107
  simp only [CollatzResearch.WordTrace]
  refine ⟨143014521405506485605417575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95343014270337657070278383 143014521405506485605417575)
  ·
    refine ⟨214521782108259728408126363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143014521405506485605417575 214521782108259728408126363)
    ·
      refine ⟨321782673162389592612189545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214521782108259728408126363 321782673162389592612189545)
      ·
        refine ⟨241337004871792194459142159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321782673162389592612189545 241337004871792194459142159)
        ·
          refine ⟨362005507307688291688713239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241337004871792194459142159 362005507307688291688713239)
          ·
            refine ⟨543008260961532437533069859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362005507307688291688713239 543008260961532437533069859)
            ·
              refine ⟨814512391442298656299604789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543008260961532437533069859 814512391442298656299604789)
              ·
                refine ⟨76360536697715499028087949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814512391442298656299604789 76360536697715499028087949)
                ·
                  refine ⟨28635201261643312135532981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76360536697715499028087949 28635201261643312135532981)
                  ·
                    refine ⟨2684550118279060512706217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28635201261643312135532981 2684550118279060512706217)
                    ·
                      refine ⟨2013412588709295384529663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684550118279060512706217 2013412588709295384529663)
                      ·
                        rfl

theorem cell23_3921107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 5, 2].length) (baseStart_3921107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921107 prefixEnd_3921107 := by exact prefixLift 3921107
  have htrace : WordTrace (prefixWord ++ tailWord_3921107) baseStart_3921107 baseEnd_3921107 := by
    simpa [prefixWord, tailWord_3921107, baseEnd_3921107] using wordTrace_append hprefix tailTrace_3921107
  have hstable : (prefixWord ++ tailWord_3921107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921107).length < 2 ^ (prefixWord ++ tailWord_3921107).sum := by decide
  have hdescent : baseEnd_3921107 < baseStart_3921107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921131 : List Nat := [1, 1, 1, 1, 2, 6, 1, 5, 1, 1, 3]
def baseStart_3921131 : Nat := 118140960795 + 3921131 * 2 ^ 59
def prefixEnd_3921131 : Nat := 4983230072969 + 3 ^ 40 * 3921131 * 2
def baseEnd_3921131 : Nat := 2013424912245003290629553

theorem tailTrace_3921131 : CollatzResearch.WordTrace tailWord_3921131 prefixEnd_3921131 2013424912245003290629553 := by
  unfold tailWord_3921131
  simp only [CollatzResearch.WordTrace]
  refine ⟨143015396757419537704291247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95343597838279691802860831 143015396757419537704291247)
  ·
    refine ⟨214523095136129306556436871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143015396757419537704291247 214523095136129306556436871)
    ·
      refine ⟨321784642704193959834655307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214523095136129306556436871 321784642704193959834655307)
      ·
        refine ⟨482676964056290939751982961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321784642704193959834655307 482676964056290939751982961)
        ·
          refine ⟨362007723042218204813987221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482676964056290939751982961 362007723042218204813987221)
          ·
            refine ⟨16969112017603978350655651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 362007723042218204813987221 16969112017603978350655651)
            ·
              refine ⟨25453668026405967525983477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969112017603978350655651 25453668026405967525983477)
              ·
                refine ⟨2386281377475559455560951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25453668026405967525983477 2386281377475559455560951)
                ·
                  refine ⟨3579422066213339183341427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386281377475559455560951 3579422066213339183341427)
                  ·
                    refine ⟨5369133099320008775012141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3579422066213339183341427 5369133099320008775012141)
                    ·
                      refine ⟨2013424912245003290629553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5369133099320008775012141 2013424912245003290629553)
                      ·
                        rfl

theorem cell23_3921131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 1, 1, 3].length) (baseStart_3921131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921131 prefixEnd_3921131 := by exact prefixLift 3921131
  have htrace : WordTrace (prefixWord ++ tailWord_3921131) baseStart_3921131 baseEnd_3921131 := by
    simpa [prefixWord, tailWord_3921131, baseEnd_3921131] using wordTrace_append hprefix tailTrace_3921131
  have hstable : (prefixWord ++ tailWord_3921131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921131).length < 2 ^ (prefixWord ++ tailWord_3921131).sum := by decide
  have hdescent : baseEnd_3921131 < baseStart_3921131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921157 : List Nat := [1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_3921157 : Nat := 118140960795 + 3921157 * 2 ^ 59
def prefixEnd_3921157 : Nat := 4983230072969 + 3 ^ 40 * 3921157 * 2
def baseEnd_3921157 : Nat := 2013438262742020188904433

theorem tailTrace_3921157 : CollatzResearch.WordTrace tailWord_3921157 prefixEnd_3921157 2013438262742020188904433 := by
  unfold tailWord_3921157
  simp only [CollatzResearch.WordTrace]
  refine ⟨143016345055325344144737725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95344230036883562763158483 143016345055325344144737725)
  ·
    refine ⟨53631129395747004054276647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143016345055325344144737725 53631129395747004054276647)
    ·
      refine ⟨80446694093620506081414971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53631129395747004054276647 80446694093620506081414971)
      ·
        refine ⟨120670041140430759122122457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80446694093620506081414971 120670041140430759122122457)
        ·
          refine ⟨90502530855323069341591843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120670041140430759122122457 90502530855323069341591843)
          ·
            refine ⟨135753796282984604012387765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90502530855323069341591843 135753796282984604012387765)
            ·
              refine ⟨12726918401529806626161353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135753796282984604012387765 12726918401529806626161353)
              ·
                refine ⟨9545188801147354969621015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12726918401529806626161353 9545188801147354969621015)
                ·
                  refine ⟨14317783201721032454431523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545188801147354969621015 14317783201721032454431523)
                  ·
                    refine ⟨21476674802581548681647285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14317783201721032454431523 21476674802581548681647285)
                    ·
                      refine ⟨2013438262742020188904433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21476674802581548681647285 2013438262742020188904433)
                      ·
                        rfl

theorem cell23_3921157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_3921157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921157 prefixEnd_3921157 := by exact prefixLift 3921157
  have htrace : WordTrace (prefixWord ++ tailWord_3921157) baseStart_3921157 baseEnd_3921157 := by
    simpa [prefixWord, tailWord_3921157, baseEnd_3921157] using wordTrace_append hprefix tailTrace_3921157
  have hstable : (prefixWord ++ tailWord_3921157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921157).length < 2 ^ (prefixWord ++ tailWord_3921157).sum := by decide
  have hdescent : baseEnd_3921157 < baseStart_3921157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921164 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_3921164 : Nat := 118140960795 + 3921164 * 2 ^ 59
def prefixEnd_3921164 : Nat := 4983230072969 + 3 ^ 40 * 3921164 * 2
def baseEnd_3921164 : Nat := 671147285702200553838967

theorem tailTrace_3921164 : CollatzResearch.WordTrace tailWord_3921164 prefixEnd_3921164 671147285702200553838967 := by
  unfold tailWord_3921164
  simp only [CollatzResearch.WordTrace]
  refine ⟨71508300183149992170121273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95344400244199989560161697 71508300183149992170121273)
  ·
    refine ⟨53631225137362494127590955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71508300183149992170121273 53631225137362494127590955)
    ·
      refine ⟨80446837706043741191386433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53631225137362494127590955 80446837706043741191386433)
      ·
        refine ⟨60335128279532805893539825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80446837706043741191386433 60335128279532805893539825)
        ·
          refine ⟨45251346209649604420154869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60335128279532805893539825 45251346209649604420154869)
          ·
            refine ⟨4242313707154650414389519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45251346209649604420154869 4242313707154650414389519)
            ·
              refine ⟨6363470560731975621584279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242313707154650414389519 6363470560731975621584279)
              ·
                refine ⟨9545205841097963432376419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6363470560731975621584279 9545205841097963432376419)
                ·
                  refine ⟨14317808761646945148564629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545205841097963432376419 14317808761646945148564629)
                  ·
                    refine ⟨671147285702200553838967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14317808761646945148564629 671147285702200553838967)
                    ·
                      rfl

theorem cell23_3921164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_3921164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921164 prefixEnd_3921164 := by exact prefixLift 3921164
  have htrace : WordTrace (prefixWord ++ tailWord_3921164) baseStart_3921164 baseEnd_3921164 := by
    simpa [prefixWord, tailWord_3921164, baseEnd_3921164] using wordTrace_append hprefix tailTrace_3921164
  have hstable : (prefixWord ++ tailWord_3921164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921164).length < 2 ^ (prefixWord ++ tailWord_3921164).sum := by decide
  have hdescent : baseEnd_3921164 < baseStart_3921164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921194 : List Nat := [3, 1, 4, 2, 1, 3, 9]
def baseStart_3921194 : Nat := 118140960795 + 3921194 * 2 ^ 59
def prefixEnd_3921194 : Nat := 4983230072969 + 3 ^ 40 * 3921194 * 2
def baseEnd_3921194 : Nat := 24857497055879463507923

theorem tailTrace_3921194 : CollatzResearch.WordTrace tailWord_3921194 prefixEnd_3921194 24857497055879463507923 := by
  unfold tailWord_3921194
  simp only [CollatzResearch.WordTrace]
  refine ⟨35754423639047824865958659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95345129704127532975889757 35754423639047824865958659)
  ·
    refine ⟨53631635458571737298937989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35754423639047824865958659 53631635458571737298937989)
    ·
      refine ⟨10055931648482200743550873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53631635458571737298937989 10055931648482200743550873)
      ·
        refine ⟨7541948736361650557663155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10055931648482200743550873 7541948736361650557663155)
        ·
          refine ⟨11312923104542475836494733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541948736361650557663155 11312923104542475836494733)
          ·
            refine ⟨4242346164203428438685525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11312923104542475836494733 4242346164203428438685525)
            ·
              refine ⟨24857497055879463507923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4242346164203428438685525 24857497055879463507923)
              ·
                rfl

theorem cell23_3921194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 9].length) (baseStart_3921194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921194 prefixEnd_3921194 := by exact prefixLift 3921194
  have htrace : WordTrace (prefixWord ++ tailWord_3921194) baseStart_3921194 baseEnd_3921194 := by
    simpa [prefixWord, tailWord_3921194, baseEnd_3921194] using wordTrace_append hprefix tailTrace_3921194
  have hstable : (prefixWord ++ tailWord_3921194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921194).length < 2 ^ (prefixWord ++ tailWord_3921194).sum := by decide
  have hdescent : baseEnd_3921194 < baseStart_3921194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921222 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3921222 : Nat := 118140960795 + 3921222 * 2 ^ 59
def prefixEnd_3921222 : Nat := 4983230072969 + 3 ^ 40 * 3921222 * 2
def baseEnd_3921222 : Nat := 2013471638984562434591635

theorem tailTrace_3921222 : CollatzResearch.WordTrace tailWord_3921222 prefixEnd_3921222 2013471638984562434591635 := by
  unfold tailWord_3921222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4469334868752808132682935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95345810533393240163902613 4469334868752808132682935)
  ·
    refine ⟨6704002303129212199024403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4469334868752808132682935 6704002303129212199024403)
    ·
      refine ⟨10056003454693818298536605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704002303129212199024403 10056003454693818298536605)
      ·
        refine ⟨3771001295510181861951227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10056003454693818298536605 3771001295510181861951227)
        ·
          refine ⟨5656501943265272792926841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771001295510181861951227 5656501943265272792926841)
          ·
            refine ⟨4242376457448954594695131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5656501943265272792926841 4242376457448954594695131)
            ·
              refine ⟨6363564686173431892042697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242376457448954594695131 6363564686173431892042697)
              ·
                refine ⟨4772673514630073919032023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6363564686173431892042697 4772673514630073919032023)
                ·
                  refine ⟨7159010271945110878548035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772673514630073919032023 7159010271945110878548035)
                  ·
                    refine ⟨10738515407917666317822053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159010271945110878548035 10738515407917666317822053)
                    ·
                      refine ⟨2013471638984562434591635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10738515407917666317822053 2013471638984562434591635)
                      ·
                        rfl

theorem cell23_3921222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3921222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921222 prefixEnd_3921222 := by exact prefixLift 3921222
  have htrace : WordTrace (prefixWord ++ tailWord_3921222) baseStart_3921222 baseEnd_3921222 := by
    simpa [prefixWord, tailWord_3921222, baseEnd_3921222] using wordTrace_append hprefix tailTrace_3921222
  have hstable : (prefixWord ++ tailWord_3921222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921222).length < 2 ^ (prefixWord ++ tailWord_3921222).sum := by decide
  have hdescent : baseEnd_3921222 < baseStart_3921222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921284 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 7]
def baseStart_3921284 : Nat := 118140960795 + 3921284 * 2 ^ 59
def prefixEnd_3921284 : Nat := 4983230072969 + 3 ^ 40 * 3921284 * 2
def baseEnd_3921284 : Nat := 223722608309460132446261

theorem tailTrace_3921284 : CollatzResearch.WordTrace tailWord_3921284 prefixEnd_3921284 223722608309460132446261 := by
  unfold tailWord_3921284
  simp only [CollatzResearch.WordTrace]
  refine ⟨71510488562932622417305453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95347318083910163223073937 71510488562932622417305453)
  ·
    refine ⟨26816433211099733406489545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71510488562932622417305453 26816433211099733406489545)
    ·
      refine ⟨20112324908324800054867159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26816433211099733406489545 20112324908324800054867159)
      ·
        refine ⟨30168487362487200082300739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20112324908324800054867159 30168487362487200082300739)
        ·
          refine ⟨45252731043730800123451109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30168487362487200082300739 45252731043730800123451109)
          ·
            refine ⟨8484887070699525023147083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45252731043730800123451109 8484887070699525023147083)
            ·
              refine ⟨12727330606049287534720625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8484887070699525023147083 12727330606049287534720625)
              ·
                refine ⟨9545497954536965651040469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12727330606049287534720625 9545497954536965651040469)
                ·
                  refine ⟨223722608309460132446261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9545497954536965651040469 223722608309460132446261)
                  ·
                    rfl

theorem cell23_3921284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_3921284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921284 prefixEnd_3921284 := by exact prefixLift 3921284
  have htrace : WordTrace (prefixWord ++ tailWord_3921284) baseStart_3921284 baseEnd_3921284 := by
    simpa [prefixWord, tailWord_3921284, baseEnd_3921284] using wordTrace_append hprefix tailTrace_3921284
  have hstable : (prefixWord ++ tailWord_3921284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921284).length < 2 ^ (prefixWord ++ tailWord_3921284).sum := by decide
  have hdescent : baseEnd_3921284 < baseStart_3921284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921297 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 1, 7]
def baseStart_3921297 : Nat := 118140960795 + 3921297 * 2 ^ 59
def prefixEnd_3921297 : Nat := 4983230072969 + 3 ^ 40 * 3921297 * 2
def baseEnd_3921297 : Nat := 671170050011216547051263

theorem tailTrace_3921297 : CollatzResearch.WordTrace tailWord_3921297 prefixEnd_3921297 671170050011216547051263 := by
  unfold tailWord_3921297
  simp only [CollatzResearch.WordTrace]
  refine ⟨143021451274818148054834145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95347634183212098703222763 143021451274818148054834145)
  ·
    refine ⟨107266088456113611041125609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143021451274818148054834145 107266088456113611041125609)
    ·
      refine ⟨80449566342085208280844207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107266088456113611041125609 80449566342085208280844207)
      ·
        refine ⟨120674349513127812421266311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80449566342085208280844207 120674349513127812421266311)
        ·
          refine ⟨181011524269691718631899467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120674349513127812421266311 181011524269691718631899467)
          ·
            refine ⟨271517286404537577947849201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181011524269691718631899467 271517286404537577947849201)
            ·
              refine ⟨203637964803403183460886901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271517286404537577947849201 203637964803403183460886901)
              ·
                refine ⟨19091059200319048449458147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203637964803403183460886901 19091059200319048449458147)
                ·
                  refine ⟨28636588800478572674187221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19091059200319048449458147 28636588800478572674187221)
                  ·
                    refine ⟨671170050011216547051263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28636588800478572674187221 671170050011216547051263)
                    ·
                      rfl

theorem cell23_3921297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_3921297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921297 prefixEnd_3921297 := by exact prefixLift 3921297
  have htrace : WordTrace (prefixWord ++ tailWord_3921297) baseStart_3921297 baseEnd_3921297 := by
    simpa [prefixWord, tailWord_3921297, baseEnd_3921297] using wordTrace_append hprefix tailTrace_3921297
  have hstable : (prefixWord ++ tailWord_3921297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921297).length < 2 ^ (prefixWord ++ tailWord_3921297).sum := by decide
  have hdescent : baseEnd_3921297 < baseStart_3921297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921391 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 6]
def baseStart_3921391 : Nat := 118140960795 + 3921391 * 2 ^ 59
def prefixEnd_3921391 : Nat := 4983230072969 + 3 ^ 40 * 3921391 * 2
def baseEnd_3921391 : Nat := 223728713023908030375373

theorem tailTrace_3921391 : CollatzResearch.WordTrace tailWord_3921391 prefixEnd_3921391 223728713023908030375373 := by
  unfold tailWord_3921391
  simp only [CollatzResearch.WordTrace]
  refine ⟨143024879736477602108756027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95349919824318401405837351 143024879736477602108756027)
  ·
    refine ⟨214537319604716403163134041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143024879736477602108756027 214537319604716403163134041)
    ·
      refine ⟨160902989703537302372350531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214537319604716403163134041 160902989703537302372350531)
      ·
        refine ⟨241354484555305953558525797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160902989703537302372350531 241354484555305953558525797)
        ·
          refine ⟨45253965854119866292223587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241354484555305953558525797 45253965854119866292223587)
          ·
            refine ⟨67880948781179799438335381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45253965854119866292223587 67880948781179799438335381)
            ·
              refine ⟨3181919474117803098671971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67880948781179799438335381 3181919474117803098671971)
              ·
                refine ⟨4772879211176704648007957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181919474117803098671971 4772879211176704648007957)
                ·
                  refine ⟨223728713023908030375373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4772879211176704648007957 223728713023908030375373)
                  ·
                    rfl

theorem cell23_3921391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 6].length) (baseStart_3921391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921391 prefixEnd_3921391 := by exact prefixLift 3921391
  have htrace : WordTrace (prefixWord ++ tailWord_3921391) baseStart_3921391 baseEnd_3921391 := by
    simpa [prefixWord, tailWord_3921391, baseEnd_3921391] using wordTrace_append hprefix tailTrace_3921391
  have hstable : (prefixWord ++ tailWord_3921391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921391).length < 2 ^ (prefixWord ++ tailWord_3921391).sum := by decide
  have hdescent : baseEnd_3921391 < baseStart_3921391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921401 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 3]
def baseStart_3921401 : Nat := 118140960795 + 3921401 * 2 ^ 59
def prefixEnd_3921401 : Nat := 4983230072969 + 3 ^ 40 * 3921401 * 2
def baseEnd_3921401 : Nat := 2013563552021717234253311

theorem tailTrace_3921401 : CollatzResearch.WordTrace tailWord_3921401 prefixEnd_3921401 2013563552021717234253311 := by
  unfold tailWord_3921401
  simp only [CollatzResearch.WordTrace]
  refine ⟨143025244466441373816620057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95350162977627582544413371 143025244466441373816620057)
  ·
    refine ⟨107268933349831030362465043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143025244466441373816620057 107268933349831030362465043)
    ·
      refine ⟨160903400024746545543697565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107268933349831030362465043 160903400024746545543697565)
      ·
        refine ⟨60338775009279954578886587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160903400024746545543697565 60338775009279954578886587)
        ·
          refine ⟨90508162513919931868329881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60338775009279954578886587 90508162513919931868329881)
          ·
            refine ⟨67881121885439948901247411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90508162513919931868329881 67881121885439948901247411)
            ·
              refine ⟨101821682828159923351871117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67881121885439948901247411 101821682828159923351871117)
              ·
                refine ⟨38183131060559971256951669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101821682828159923351871117 38183131060559971256951669)
                ·
                  refine ⟨3579668536927497305339219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38183131060559971256951669 3579668536927497305339219)
                  ·
                    refine ⟨5369502805391245958008829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3579668536927497305339219 5369502805391245958008829)
                    ·
                      refine ⟨2013563552021717234253311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5369502805391245958008829 2013563552021717234253311)
                      ·
                        rfl

theorem cell23_3921401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_3921401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921401 prefixEnd_3921401 := by exact prefixLift 3921401
  have htrace : WordTrace (prefixWord ++ tailWord_3921401) baseStart_3921401 baseEnd_3921401 := by
    simpa [prefixWord, tailWord_3921401, baseEnd_3921401] using wordTrace_append hprefix tailTrace_3921401
  have hstable : (prefixWord ++ tailWord_3921401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921401).length < 2 ^ (prefixWord ++ tailWord_3921401).sum := by decide
  have hdescent : baseEnd_3921401 < baseStart_3921401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921434 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_3921434 : Nat := 118140960795 + 3921434 * 2 ^ 59
def prefixEnd_3921434 : Nat := 4983230072969 + 3 ^ 40 * 3921434 * 2
def baseEnd_3921434 : Nat := 671193498961105201713553

theorem tailTrace_3921434 : CollatzResearch.WordTrace tailWord_3921434 prefixEnd_3921434 671193498961105201713553 := by
  unfold tailWord_3921434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35756612018830455113142839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95350965383547880301714237 35756612018830455113142839)
  ·
    refine ⟨53634918028245682669714259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35756612018830455113142839 53634918028245682669714259)
    ·
      refine ⟨80452377042368524004571389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53634918028245682669714259 80452377042368524004571389)
      ·
        refine ⟨30169641390888196501714271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80452377042368524004571389 30169641390888196501714271)
        ·
          refine ⟨45254462086332294752571407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30169641390888196501714271 45254462086332294752571407)
          ·
            refine ⟨67881693129498442128857111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45254462086332294752571407 67881693129498442128857111)
            ·
              refine ⟨101822539694247663193285667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67881693129498442128857111 101822539694247663193285667)
              ·
                refine ⟨152733809541371494789928501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101822539694247663193285667 152733809541371494789928501)
                ·
                  refine ⟨14318794644503577636555797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152733809541371494789928501 14318794644503577636555797)
                  ·
                    refine ⟨671193498961105201713553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14318794644503577636555797 671193498961105201713553)
                    ·
                      rfl

theorem cell23_3921434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_3921434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921434 prefixEnd_3921434 := by exact prefixLift 3921434
  have htrace : WordTrace (prefixWord ++ tailWord_3921434) baseStart_3921434 baseEnd_3921434 := by
    simpa [prefixWord, tailWord_3921434, baseEnd_3921434] using wordTrace_append hprefix tailTrace_3921434
  have hstable : (prefixWord ++ tailWord_3921434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921434).length < 2 ^ (prefixWord ++ tailWord_3921434).sum := by decide
  have hdescent : baseEnd_3921434 < baseStart_3921434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921441 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3921441 : Nat := 118140960795 + 3921441 * 2 ^ 59
def prefixEnd_3921441 : Nat := 4983230072969 + 3 ^ 40 * 3921441 * 2
def baseEnd_3921441 : Nat := 2013584091247897077753127

theorem tailTrace_3921441 : CollatzResearch.WordTrace tailWord_3921441 prefixEnd_3921441 2013584091247897077753127 := by
  unfold tailWord_3921441
  simp only [CollatzResearch.WordTrace]
  refine ⟨143026703386296460648076177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95351135590864307098717451 143026703386296460648076177)
  ·
    refine ⟨107270027539722345486057133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143026703386296460648076177 107270027539722345486057133)
    ·
      refine ⟨40226260327395879557271425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107270027539722345486057133 40226260327395879557271425)
      ·
        refine ⟨30169695245546909667953569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40226260327395879557271425 30169695245546909667953569)
        ·
          refine ⟨22627271434160182250965177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30169695245546909667953569 22627271434160182250965177)
          ·
            refine ⟨16970453575620136688223883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22627271434160182250965177 16970453575620136688223883)
            ·
              refine ⟨25455680363430205032335825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16970453575620136688223883 25455680363430205032335825)
              ·
                refine ⟨19091760272572653774251869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25455680363430205032335825 19091760272572653774251869)
                ·
                  refine ⟨7159410102214745165344451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19091760272572653774251869 7159410102214745165344451)
                  ·
                    refine ⟨10739115153322117748016677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159410102214745165344451 10739115153322117748016677)
                    ·
                      refine ⟨2013584091247897077753127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10739115153322117748016677 2013584091247897077753127)
                      ·
                        rfl

theorem cell23_3921441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3921441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921441 prefixEnd_3921441 := by exact prefixLift 3921441
  have htrace : WordTrace (prefixWord ++ tailWord_3921441) baseStart_3921441 baseEnd_3921441 := by
    simpa [prefixWord, tailWord_3921441, baseEnd_3921441] using wordTrace_append hprefix tailTrace_3921441
  have hstable : (prefixWord ++ tailWord_3921441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921441).length < 2 ^ (prefixWord ++ tailWord_3921441).sum := by decide
  have hdescent : baseEnd_3921441 < baseStart_3921441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921471 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 4]
def baseStart_3921471 : Nat := 118140960795 + 3921471 * 2 ^ 59
def prefixEnd_3921471 : Nat := 4983230072969 + 3 ^ 40 * 3921471 * 2
def baseEnd_3921471 : Nat := 2013599495667531960377989

theorem tailTrace_3921471 : CollatzResearch.WordTrace tailWord_3921471 prefixEnd_3921471 2013599495667531960377989 := by
  unfold tailWord_3921471
  simp only [CollatzResearch.WordTrace]
  refine ⟨143027797576187775771668267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95351865050791850514445511 143027797576187775771668267)
  ·
    refine ⟨214541696364281663657502401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143027797576187775771668267 214541696364281663657502401)
    ·
      refine ⟨160906272273211247743126801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214541696364281663657502401 160906272273211247743126801)
      ·
        refine ⟨120679704204908435807345101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160906272273211247743126801 120679704204908435807345101)
        ·
          refine ⟨45254889076840663427754413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120679704204908435807345101 45254889076840663427754413)
          ·
            refine ⟨16970583403815248785407905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45254889076840663427754413 16970583403815248785407905)
            ·
              refine ⟨12727937552861436589055929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16970583403815248785407905 12727937552861436589055929)
              ·
                refine ⟨9545953164646077441791947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12727937552861436589055929 9545953164646077441791947)
                ·
                  refine ⟨14318929746969116162687921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9545953164646077441791947 14318929746969116162687921)
                  ·
                    refine ⟨10739197310226837122015941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14318929746969116162687921 10739197310226837122015941)
                    ·
                      refine ⟨2013599495667531960377989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10739197310226837122015941 2013599495667531960377989)
                      ·
                        rfl

theorem cell23_3921471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 4].length) (baseStart_3921471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921471 prefixEnd_3921471 := by exact prefixLift 3921471
  have htrace : WordTrace (prefixWord ++ tailWord_3921471) baseStart_3921471 baseEnd_3921471 := by
    simpa [prefixWord, tailWord_3921471, baseEnd_3921471] using wordTrace_append hprefix tailTrace_3921471
  have hstable : (prefixWord ++ tailWord_3921471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921471).length < 2 ^ (prefixWord ++ tailWord_3921471).sum := by decide
  have hdescent : baseEnd_3921471 < baseStart_3921471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921485 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3921485 : Nat := 118140960795 + 3921485 * 2 ^ 59
def prefixEnd_3921485 : Nat := 4983230072969 + 3 ^ 40 * 3921485 * 2
def baseEnd_3921485 : Nat := 671202228132231635200975

theorem tailTrace_3921485 : CollatzResearch.WordTrace tailWord_3921485 prefixEnd_3921485 671202228132231635200975 := by
  unfold tailWord_3921485
  simp only [CollatzResearch.WordTrace]
  refine ⟨143028308198137056162677909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95352205465424704108451939 143028308198137056162677909)
  ·
    refine ⟨6704451946787674507625527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143028308198137056162677909 6704451946787674507625527)
    ·
      refine ⟨10056677920181511761438291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704451946787674507625527 10056677920181511761438291)
      ·
        refine ⟨15085016880272267642157437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10056677920181511761438291 15085016880272267642157437)
        ·
          refine ⟨5656881330102100365809039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15085016880272267642157437 5656881330102100365809039)
          ·
            refine ⟨8485321995153150548713559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656881330102100365809039 8485321995153150548713559)
            ·
              refine ⟨12727982992729725823070339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485321995153150548713559 12727982992729725823070339)
              ·
                refine ⟨19091974489094588734605509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12727982992729725823070339 19091974489094588734605509)
                ·
                  refine ⟨3579745216705235387738533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19091974489094588734605509 3579745216705235387738533)
                  ·
                    refine ⟨671202228132231635200975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3579745216705235387738533 671202228132231635200975)
                    ·
                      rfl

theorem cell23_3921485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3921485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921485 prefixEnd_3921485 := by exact prefixLift 3921485
  have htrace : WordTrace (prefixWord ++ tailWord_3921485) baseStart_3921485 baseEnd_3921485 := by
    simpa [prefixWord, tailWord_3921485, baseEnd_3921485] using wordTrace_append hprefix tailTrace_3921485
  have hstable : (prefixWord ++ tailWord_3921485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921485).length < 2 ^ (prefixWord ++ tailWord_3921485).sum := by decide
  have hdescent : baseEnd_3921485 < baseStart_3921485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921492 : List Nat := [2, 4, 1, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_3921492 : Nat := 118140960795 + 3921492 * 2 ^ 59
def prefixEnd_3921492 : Nat := 4983230072969 + 3 ^ 40 * 3921492 * 2
def baseEnd_3921492 : Nat := 2013610278761276378215393

theorem tailTrace_3921492 : CollatzResearch.WordTrace tailWord_3921492 prefixEnd_3921492 2013610278761276378215393 := by
  unfold tailWord_3921492
  simp only [CollatzResearch.WordTrace]
  refine ⟨71514281754555848179091365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95352375672741130905455153 71514281754555848179091365)
  ·
    refine ⟨13408927828979221533579631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71514281754555848179091365 13408927828979221533579631)
    ·
      refine ⟨20113391743468832300369447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13408927828979221533579631 20113391743468832300369447)
      ·
        refine ⟨30170087615203248450554171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20113391743468832300369447 30170087615203248450554171)
        ·
          refine ⟨45255131422804872675831257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30170087615203248450554171 45255131422804872675831257)
          ·
            refine ⟨33941348567103654506873443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45255131422804872675831257 33941348567103654506873443)
            ·
              refine ⟨50912022850655481760310165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33941348567103654506873443 50912022850655481760310165)
              ·
                refine ⟨2386501071124475707514539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50912022850655481760310165 2386501071124475707514539)
                ·
                  refine ⟨3579751606686713561271809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386501071124475707514539 3579751606686713561271809)
                  ·
                    refine ⟨2684813705015035170953857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3579751606686713561271809 2684813705015035170953857)
                    ·
                      refine ⟨2013610278761276378215393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684813705015035170953857 2013610278761276378215393)
                      ·
                        rfl

theorem cell23_3921492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_3921492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921492 prefixEnd_3921492 := by exact prefixLift 3921492
  have htrace : WordTrace (prefixWord ++ tailWord_3921492) baseStart_3921492 baseEnd_3921492 := by
    simpa [prefixWord, tailWord_3921492, baseEnd_3921492] using wordTrace_append hprefix tailTrace_3921492
  have hstable : (prefixWord ++ tailWord_3921492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921492).length < 2 ^ (prefixWord ++ tailWord_3921492).sum := by decide
  have hdescent : baseEnd_3921492 < baseStart_3921492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921508 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_3921508 : Nat := 118140960795 + 3921508 * 2 ^ 59
def prefixEnd_3921508 : Nat := 4983230072969 + 3 ^ 40 * 3921508 * 2
def baseEnd_3921508 : Nat := 2013618494451748315615319

theorem tailTrace_3921508 : CollatzResearch.WordTrace tailWord_3921508 prefixEnd_3921508 2013618494451748315615319 := by
  unfold tailWord_3921508
  simp only [CollatzResearch.WordTrace]
  refine ⟨71514573538526865545382589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95352764718035820727176785 71514573538526865545382589)
  ·
    refine ⟨26817965076947574579518471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71514573538526865545382589 26817965076947574579518471)
    ·
      refine ⟨40226947615421361869277707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26817965076947574579518471 40226947615421361869277707)
      ·
        refine ⟨60340421423132042803916561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40226947615421361869277707 60340421423132042803916561)
        ·
          refine ⟨45255316067349032102937421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60340421423132042803916561 45255316067349032102937421)
          ·
            refine ⟨16970743525255887038601533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45255316067349032102937421 16970743525255887038601533)
            ·
              refine ⟨6364028821970957639475575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16970743525255887038601533 6364028821970957639475575)
              ·
                refine ⟨9546043232956436459213363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364028821970957639475575 9546043232956436459213363)
                ·
                  refine ⟨14319064849434654688820045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9546043232956436459213363 14319064849434654688820045)
                  ·
                    refine ⟨5369649318537995508307517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14319064849434654688820045 5369649318537995508307517)
                    ·
                      refine ⟨2013618494451748315615319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5369649318537995508307517 2013618494451748315615319)
                      ·
                        rfl

theorem cell23_3921508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_3921508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921508 prefixEnd_3921508 := by exact prefixLift 3921508
  have htrace : WordTrace (prefixWord ++ tailWord_3921508) baseStart_3921508 baseEnd_3921508 := by
    simpa [prefixWord, tailWord_3921508, baseEnd_3921508] using wordTrace_append hprefix tailTrace_3921508
  have hstable : (prefixWord ++ tailWord_3921508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921508).length < 2 ^ (prefixWord ++ tailWord_3921508).sum := by decide
  have hdescent : baseEnd_3921508 < baseStart_3921508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921525 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3921525 : Nat := 118140960795 + 3921525 * 2 ^ 59
def prefixEnd_3921525 : Nat := 4983230072969 + 3 ^ 40 * 3921525 * 2
def baseEnd_3921525 : Nat := 2013627223622874749102741

theorem tailTrace_3921525 : CollatzResearch.WordTrace tailWord_3921525 prefixEnd_3921525 2013627223622874749102741 := by
  unfold tailWord_3921525
  simp only [CollatzResearch.WordTrace]
  refine ⟨143029767117992142994134029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95353178078661428662756019 143029767117992142994134029)
  ·
    refine ⟨53636162669247053622800261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143029767117992142994134029 53636162669247053622800261)
    ·
      refine ⟨10056780500483822554275049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53636162669247053622800261 10056780500483822554275049)
      ·
        refine ⟨7542585375362866915706287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10056780500483822554275049 7542585375362866915706287)
        ·
          refine ⟨11313878063044300373559431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542585375362866915706287 11313878063044300373559431)
          ·
            refine ⟨16970817094566450560339147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11313878063044300373559431 16970817094566450560339147)
            ·
              refine ⟨25456225641849675840508721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16970817094566450560339147 25456225641849675840508721)
              ·
                refine ⟨19092169231387256880381541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25456225641849675840508721 19092169231387256880381541)
                ·
                  refine ⟨3579781730885110665071539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19092169231387256880381541 3579781730885110665071539)
                  ·
                    refine ⟨5369672596327665997607309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3579781730885110665071539 5369672596327665997607309)
                    ·
                      refine ⟨2013627223622874749102741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5369672596327665997607309 2013627223622874749102741)
                      ·
                        rfl

theorem cell23_3921525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3921525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921525 prefixEnd_3921525 := by exact prefixLift 3921525
  have htrace : WordTrace (prefixWord ++ tailWord_3921525) baseStart_3921525 baseEnd_3921525 := by
    simpa [prefixWord, tailWord_3921525, baseEnd_3921525] using wordTrace_append hprefix tailTrace_3921525
  have hstable : (prefixWord ++ tailWord_3921525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921525).length < 2 ^ (prefixWord ++ tailWord_3921525).sum := by decide
  have hdescent : baseEnd_3921525 < baseStart_3921525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921526 : List Nat := [5, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3921526 : Nat := 118140960795 + 3921526 * 2 ^ 59
def prefixEnd_3921526 : Nat := 4983230072969 + 3 ^ 40 * 3921526 * 2
def baseEnd_3921526 : Nat := 2013627737103529245190237

theorem tailTrace_3921526 : CollatzResearch.WordTrace tailWord_3921526 prefixEnd_3921526 2013627737103529245190237 := by
  unfold tailWord_3921526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939362724436782510307527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95353202393992346776613621 8939362724436782510307527)
  ·
    refine ⟨13409044086655173765461291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8939362724436782510307527 13409044086655173765461291)
    ·
      refine ⟨20113566129982760648191937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13409044086655173765461291 20113566129982760648191937)
      ·
        refine ⟨15085174597487070486143953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20113566129982760648191937 15085174597487070486143953)
        ·
          refine ⟨11313880948115302864607965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15085174597487070486143953 11313880948115302864607965)
          ·
            refine ⟨4242705355543238574227987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11313880948115302864607965 4242705355543238574227987)
            ·
              refine ⟨6364058033314857861341981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242705355543238574227987 6364058033314857861341981)
              ·
                refine ⟨2386521762493071698003243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6364058033314857861341981 2386521762493071698003243)
                ·
                  refine ⟨3579782643739607547004865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386521762493071698003243 3579782643739607547004865)
                  ·
                    refine ⟨2684836982804705660253649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3579782643739607547004865 2684836982804705660253649)
                    ·
                      refine ⟨2013627737103529245190237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684836982804705660253649 2013627737103529245190237)
                      ·
                        rfl

theorem cell23_3921526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3921526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921526 prefixEnd_3921526 := by exact prefixLift 3921526
  have htrace : WordTrace (prefixWord ++ tailWord_3921526) baseStart_3921526 baseEnd_3921526 := by
    simpa [prefixWord, tailWord_3921526, baseEnd_3921526] using wordTrace_append hprefix tailTrace_3921526
  have hstable : (prefixWord ++ tailWord_3921526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921526).length < 2 ^ (prefixWord ++ tailWord_3921526).sum := by decide
  have hdescent : baseEnd_3921526 < baseStart_3921526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921608 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_3921608 : Nat := 118140960795 + 3921608 * 2 ^ 59
def prefixEnd_3921608 : Nat := 4983230072969 + 3 ^ 40 * 3921608 * 2
def baseEnd_3921608 : Nat := 2013669842517197924364859

theorem tailTrace_3921608 : CollatzResearch.WordTrace tailWord_3921608 prefixEnd_3921608 2013669842517197924364859 := by
  unfold tailWord_3921608
  simp only [CollatzResearch.WordTrace]
  refine ⟨71516397188345724084702739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95355196251127632112936985 71516397188345724084702739)
  ·
    refine ⟨107274595782518586127054109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71516397188345724084702739 107274595782518586127054109)
    ·
      refine ⟨40227973418444469797645291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107274595782518586127054109 40227973418444469797645291)
      ·
        refine ⟨60341960127666704696467937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40227973418444469797645291 60341960127666704696467937)
        ·
          refine ⟨45256470095750028522350953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60341960127666704696467937 45256470095750028522350953)
          ·
            refine ⟨33942352571812521391763215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45256470095750028522350953 33942352571812521391763215)
            ·
              refine ⟨50913528857718782087644823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33942352571812521391763215 50913528857718782087644823)
              ·
                refine ⟨76370293286578173131467235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50913528857718782087644823 76370293286578173131467235)
                ·
                  refine ⟨114555439929867259697200853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76370293286578173131467235 114555439929867259697200853)
                  ·
                    refine ⟨2684893123356263899153145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 114555439929867259697200853 2684893123356263899153145)
                    ·
                      refine ⟨2013669842517197924364859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2684893123356263899153145 2013669842517197924364859)
                      ·
                        rfl

theorem cell23_3921608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_3921608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921608 prefixEnd_3921608 := by exact prefixLift 3921608
  have htrace : WordTrace (prefixWord ++ tailWord_3921608) baseStart_3921608 baseEnd_3921608 := by
    simpa [prefixWord, tailWord_3921608, baseEnd_3921608] using wordTrace_append hprefix tailTrace_3921608
  have hstable : (prefixWord ++ tailWord_3921608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921608).length < 2 ^ (prefixWord ++ tailWord_3921608).sum := by decide
  have hdescent : baseEnd_3921608 < baseStart_3921608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921622 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3921622 : Nat := 118140960795 + 3921622 * 2 ^ 59
def prefixEnd_3921622 : Nat := 4983230072969 + 3 ^ 40 * 3921622 * 2
def baseEnd_3921622 : Nat := 223741892360706763287755

theorem tailTrace_3921622 : CollatzResearch.WordTrace tailWord_3921622 prefixEnd_3921622 223741892360706763287755 := by
  unfold tailWord_3921622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939581562415045535025945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95355536665760485706943413 8939581562415045535025945)
  ·
    refine ⟨6704686171811284151269459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8939581562415045535025945 6704686171811284151269459)
    ·
      refine ⟨10057029257716926226904189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704686171811284151269459 10057029257716926226904189)
      ·
        refine ⟨3771385971643847335089071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10057029257716926226904189 3771385971643847335089071)
        ·
          refine ⟨5657078957465771002633607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771385971643847335089071 5657078957465771002633607)
          ·
            refine ⟨8485618436198656503950411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657078957465771002633607 8485618436198656503950411)
            ·
              refine ⟨12728427654297984755925617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485618436198656503950411 12728427654297984755925617)
              ·
                refine ⟨9546320740723488566944213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12728427654297984755925617 9546320740723488566944213)
                ·
                  refine ⟨223741892360706763287755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9546320740723488566944213 223741892360706763287755)
                  ·
                    rfl

theorem cell23_3921622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3921622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921622 prefixEnd_3921622 := by exact prefixLift 3921622
  have htrace : WordTrace (prefixWord ++ tailWord_3921622) baseStart_3921622 baseEnd_3921622 := by
    simpa [prefixWord, tailWord_3921622, baseEnd_3921622] using wordTrace_append hprefix tailTrace_3921622
  have hstable : (prefixWord ++ tailWord_3921622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921622).length < 2 ^ (prefixWord ++ tailWord_3921622).sum := by decide
  have hdescent : baseEnd_3921622 < baseStart_3921622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921651 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6]
def baseStart_3921651 : Nat := 118140960795 + 3921651 * 2 ^ 59
def prefixEnd_3921651 : Nat := 4983230072969 + 3 ^ 40 * 3921651 * 2
def baseEnd_3921651 : Nat := 2013691922185341256127161

theorem tailTrace_3921651 : CollatzResearch.WordTrace tailWord_3921651 prefixEnd_3921651 2013691922185341256127161 := by
  unfold tailWord_3921651
  simp only [CollatzResearch.WordTrace]
  refine ⟨143034362715535666513220807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95356241810357111008813871 143034362715535666513220807)
  ·
    refine ⟨214551544073303499769831211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143034362715535666513220807 214551544073303499769831211)
    ·
      refine ⟨321827316109955249654746817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214551544073303499769831211 321827316109955249654746817)
      ·
        refine ⟨241370487082466437241060113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321827316109955249654746817 241370487082466437241060113)
        ·
          refine ⟨181027865311849827930795085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241370487082466437241060113 181027865311849827930795085)
          ·
            refine ⟨67885449491943685474048157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181027865311849827930795085 67885449491943685474048157)
            ·
              refine ⟨25457043559478882052768059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67885449491943685474048157 25457043559478882052768059)
              ·
                refine ⟨38185565339218323079152089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25457043559478882052768059 38185565339218323079152089)
                ·
                  refine ⟨28639174004413742309364067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38185565339218323079152089 28639174004413742309364067)
                  ·
                    refine ⟨42958761006620613464046101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28639174004413742309364067 42958761006620613464046101)
                    ·
                      refine ⟨2013691922185341256127161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42958761006620613464046101 2013691922185341256127161)
                      ·
                        rfl

theorem cell23_3921651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_3921651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921651 prefixEnd_3921651 := by exact prefixLift 3921651
  have htrace : WordTrace (prefixWord ++ tailWord_3921651) baseStart_3921651 baseEnd_3921651 := by
    simpa [prefixWord, tailWord_3921651, baseEnd_3921651] using wordTrace_append hprefix tailTrace_3921651
  have hstable : (prefixWord ++ tailWord_3921651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921651).length < 2 ^ (prefixWord ++ tailWord_3921651).sum := by decide
  have hdescent : baseEnd_3921651 < baseStart_3921651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921658 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_3921658 : Nat := 118140960795 + 3921658 * 2 ^ 59
def prefixEnd_3921658 : Nat := 4983230072969 + 3 ^ 40 * 3921658 * 2
def baseEnd_3921658 : Nat := 2013695516549922728739629

theorem tailTrace_3921658 : CollatzResearch.WordTrace tailWord_3921658 prefixEnd_3921658 2013695516549922728739629 := by
  unfold tailWord_3921658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35758654506627576677181407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95356412017673537805817085 35758654506627576677181407)
  ·
    refine ⟨53637981759941365015772111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35758654506627576677181407 53637981759941365015772111)
    ·
      refine ⟨80456972639912047523658167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53637981759941365015772111 80456972639912047523658167)
      ·
        refine ⟨120685458959868071285487251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80456972639912047523658167 120685458959868071285487251)
        ·
          refine ⟨181028188439802106928230877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120685458959868071285487251 181028188439802106928230877)
          ·
            refine ⟨67885570664925790098086579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181028188439802106928230877 67885570664925790098086579)
            ·
              refine ⟨101828355997388685147129869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67885570664925790098086579 101828355997388685147129869)
              ·
                refine ⟨38185633499020756930173701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101828355997388685147129869 38185633499020756930173701)
                ·
                  refine ⟨7159806281066391924407569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38185633499020756930173701 7159806281066391924407569)
                  ·
                    refine ⟨5369854710799793943305677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7159806281066391924407569 5369854710799793943305677)
                    ·
                      refine ⟨2013695516549922728739629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5369854710799793943305677 2013695516549922728739629)
                      ·
                        rfl

theorem cell23_3921658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_3921658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921658 prefixEnd_3921658 := by exact prefixLift 3921658
  have htrace : WordTrace (prefixWord ++ tailWord_3921658) baseStart_3921658 baseEnd_3921658 := by
    simpa [prefixWord, tailWord_3921658, baseEnd_3921658] using wordTrace_append hprefix tailTrace_3921658
  have hstable : (prefixWord ++ tailWord_3921658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921658).length < 2 ^ (prefixWord ++ tailWord_3921658).sum := by decide
  have hdescent : baseEnd_3921658 < baseStart_3921658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921678 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_3921678 : Nat := 118140960795 + 3921678 * 2 ^ 59
def prefixEnd_3921678 : Nat := 4983230072969 + 3 ^ 40 * 3921678 * 2
def baseEnd_3921678 : Nat := 223745087351445850054393

theorem tailTrace_3921678 : CollatzResearch.WordTrace tailWord_3921678 prefixEnd_3921678 223745087351445850054393 := by
  unfold tailWord_3921678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17879418435804731265556711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95356898324291900082969125 17879418435804731265556711)
  ·
    refine ⟨26819127653707096898335067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17879418435804731265556711 26819127653707096898335067)
    ·
      refine ⟨40228691480560645347502601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26819127653707096898335067 40228691480560645347502601)
      ·
        refine ⟨30171518610420484010626951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40228691480560645347502601 30171518610420484010626951)
        ·
          refine ⟨45257277915630726015940427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30171518610420484010626951 45257277915630726015940427)
          ·
            refine ⟨67885916873446089023910641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45257277915630726015940427 67885916873446089023910641)
            ·
              refine ⟨50914437655084566767932981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67885916873446089023910641 50914437655084566767932981)
              ·
                refine ⟨4773228530164178134493717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50914437655084566767932981 4773228530164178134493717)
                ·
                  refine ⟨223745087351445850054393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4773228530164178134493717 223745087351445850054393)
                  ·
                    rfl

theorem cell23_3921678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_3921678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921678 prefixEnd_3921678 := by exact prefixLift 3921678
  have htrace : WordTrace (prefixWord ++ tailWord_3921678) baseStart_3921678 baseEnd_3921678 := by
    simpa [prefixWord, tailWord_3921678, baseEnd_3921678] using wordTrace_append hprefix tailTrace_3921678
  have hstable : (prefixWord ++ tailWord_3921678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921678).length < 2 ^ (prefixWord ++ tailWord_3921678).sum := by decide
  have hdescent : baseEnd_3921678 < baseStart_3921678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921681 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_3921681 : Nat := 118140960795 + 3921681 * 2 ^ 59
def prefixEnd_3921681 : Nat := 4983230072969 + 3 ^ 40 * 3921681 * 2
def baseEnd_3921681 : Nat := 2013707326604976138752023

theorem tailTrace_3921681 : CollatzResearch.WordTrace tailWord_3921681 prefixEnd_3921681 2013707326604976138752023 := by
  unfold tailWord_3921681
  simp only [CollatzResearch.WordTrace]
  refine ⟨143035456905426981636812897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95356971270284654424541931 143035456905426981636812897)
  ·
    refine ⟨107276592679070236227609673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143035456905426981636812897 107276592679070236227609673)
    ·
      refine ⟨80457444509302677170707255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107276592679070236227609673 80457444509302677170707255)
      ·
        refine ⟨120686166763954015756060883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80457444509302677170707255 120686166763954015756060883)
        ·
          refine ⟨181029250145931023634091325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120686166763954015756060883 181029250145931023634091325)
          ·
            refine ⟨67885968804724133862784247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181029250145931023634091325 67885968804724133862784247)
            ·
              refine ⟨101828953207086200794176371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67885968804724133862784247 101828953207086200794176371)
              ·
                refine ⟨152743429810629301191264557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101828953207086200794176371 152743429810629301191264557)
                ·
                  refine ⟨57278786178985987946724209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152743429810629301191264557 57278786178985987946724209)
                  ·
                    refine ⟨42959089634239490960043157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57278786178985987946724209 42959089634239490960043157)
                    ·
                      refine ⟨2013707326604976138752023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42959089634239490960043157 2013707326604976138752023)
                      ·
                        rfl

theorem cell23_3921681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_3921681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921681 prefixEnd_3921681 := by exact prefixLift 3921681
  have htrace : WordTrace (prefixWord ++ tailWord_3921681) baseStart_3921681 baseEnd_3921681 := by
    simpa [prefixWord, tailWord_3921681, baseEnd_3921681] using wordTrace_append hprefix tailTrace_3921681
  have hstable : (prefixWord ++ tailWord_3921681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921681).length < 2 ^ (prefixWord ++ tailWord_3921681).sum := by decide
  have hdescent : baseEnd_3921681 < baseStart_3921681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921682 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3921682 : Nat := 118140960795 + 3921682 * 2 ^ 59
def prefixEnd_3921682 : Nat := 4983230072969 + 3 ^ 40 * 3921682 * 2
def baseEnd_3921682 : Nat := 671235946695210211613173

theorem tailTrace_3921682 : CollatzResearch.WordTrace tailWord_3921682 prefixEnd_3921682 671235946695210211613173 := by
  unfold tailWord_3921682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35758873344605839701899825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95356995585615572538399533 35758873344605839701899825)
  ·
    refine ⟨26819155008454379776424869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35758873344605839701899825 26819155008454379776424869)
    ·
      refine ⟨5028591564085196208079663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26819155008454379776424869 5028591564085196208079663)
      ·
        refine ⟨7542887346127794312119495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028591564085196208079663 7542887346127794312119495)
        ·
          refine ⟨11314331019191691468179243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7542887346127794312119495 11314331019191691468179243)
          ·
            refine ⟨16971496528787537202268865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11314331019191691468179243 16971496528787537202268865)
            ·
              refine ⟨12728622396590652901701649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16971496528787537202268865 12728622396590652901701649)
              ·
                refine ⟨9546466797442989676276237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12728622396590652901701649 9546466797442989676276237)
                ·
                  refine ⟨3579925049041121128603589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9546466797442989676276237 3579925049041121128603589)
                  ·
                    refine ⟨671235946695210211613173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3579925049041121128603589 671235946695210211613173)
                    ·
                      rfl

theorem cell23_3921682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3921682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921682 prefixEnd_3921682 := by exact prefixLift 3921682
  have htrace : WordTrace (prefixWord ++ tailWord_3921682) baseStart_3921682 baseEnd_3921682 := by
    simpa [prefixWord, tailWord_3921682, baseEnd_3921682] using wordTrace_append hprefix tailTrace_3921682
  have hstable : (prefixWord ++ tailWord_3921682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921682).length < 2 ^ (prefixWord ++ tailWord_3921682).sum := by decide
  have hdescent : baseEnd_3921682 < baseStart_3921682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921716 : List Nat := [2, 5, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3921716 : Nat := 118140960795 + 3921716 * 2 ^ 59
def prefixEnd_3921716 : Nat := 4983230072969 + 3 ^ 40 * 3921716 * 2
def baseEnd_3921716 : Nat := 671241766142627833938121

theorem tailTrace_3921716 : CollatzResearch.WordTrace tailWord_3921716 prefixEnd_3921716 671241766142627833938121 := by
  unfold tailWord_3921716
  simp only [CollatzResearch.WordTrace]
  refine ⟨71518366730150091307168501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95357822306866788409558001 71518366730150091307168501)
  ·
    refine ⟨6704846880951571060047047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71518366730150091307168501 6704846880951571060047047)
    ·
      refine ⟨10057270321427356590070571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6704846880951571060047047 10057270321427356590070571)
      ·
        refine ⟨15085905482141034885105857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057270321427356590070571 15085905482141034885105857)
        ·
          refine ⟨11314429111605776163829393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15085905482141034885105857 11314429111605776163829393)
          ·
            refine ⟨8485821833704332122872045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11314429111605776163829393 8485821833704332122872045)
            ·
              refine ⟨3182183187639124546077017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8485821833704332122872045 3182183187639124546077017)
              ·
                refine ⟨2386637390729343409557763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182183187639124546077017 2386637390729343409557763)
                ·
                  refine ⟨3579956086094015114336645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386637390729343409557763 3579956086094015114336645)
                  ·
                    refine ⟨671241766142627833938121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3579956086094015114336645 671241766142627833938121)
                    ·
                      rfl

theorem cell23_3921716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3921716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921716 prefixEnd_3921716 := by exact prefixLift 3921716
  have htrace : WordTrace (prefixWord ++ tailWord_3921716) baseStart_3921716 baseEnd_3921716 := by
    simpa [prefixWord, tailWord_3921716, baseEnd_3921716] using wordTrace_append hprefix tailTrace_3921716
  have hstable : (prefixWord ++ tailWord_3921716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921716).length < 2 ^ (prefixWord ++ tailWord_3921716).sum := by decide
  have hdescent : baseEnd_3921716 < baseStart_3921716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921722 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_3921722 : Nat := 118140960795 + 3921722 * 2 ^ 59
def prefixEnd_3921722 : Nat := 4983230072969 + 3 ^ 40 * 3921722 * 2
def baseEnd_3921722 : Nat := 2013728379311810478339335

theorem tailTrace_3921722 : CollatzResearch.WordTrace tailWord_3921722 prefixEnd_3921722 2013728379311810478339335 := by
  unfold tailWord_3921722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35759238074569611409763855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95357968198852297092703613 35759238074569611409763855)
  ·
    refine ⟨53638857111854417114645783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35759238074569611409763855 53638857111854417114645783)
    ·
      refine ⟨80458285667781625671968675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53638857111854417114645783 80458285667781625671968675)
      ·
        refine ⟨120687428501672438507953013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80458285667781625671968675 120687428501672438507953013)
        ·
          refine ⟨11314446422031791110120595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120687428501672438507953013 11314446422031791110120595)
          ·
            refine ⟨16971669633047686665180893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11314446422031791110120595 16971669633047686665180893)
            ·
              refine ⟨6364376112392882499442835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16971669633047686665180893 6364376112392882499442835)
              ·
                refine ⟨9546564168589323749164253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364376112392882499442835 9546564168589323749164253)
                ·
                  refine ⟨3579961563220996405936595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9546564168589323749164253 3579961563220996405936595)
                  ·
                    refine ⟨5369942344831494608904893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3579961563220996405936595 5369942344831494608904893)
                    ·
                      refine ⟨2013728379311810478339335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5369942344831494608904893 2013728379311810478339335)
                      ·
                        rfl

theorem cell23_3921722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_3921722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921722 prefixEnd_3921722 := by exact prefixLift 3921722
  have htrace : WordTrace (prefixWord ++ tailWord_3921722) baseStart_3921722 baseEnd_3921722 := by
    simpa [prefixWord, tailWord_3921722, baseEnd_3921722] using wordTrace_append hprefix tailTrace_3921722
  have hstable : (prefixWord ++ tailWord_3921722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921722).length < 2 ^ (prefixWord ++ tailWord_3921722).sum := by decide
  have hdescent : baseEnd_3921722 < baseStart_3921722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921738 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 1, 6]
def baseStart_3921738 : Nat := 118140960795 + 3921738 * 2 ^ 59
def prefixEnd_3921738 : Nat := 4983230072969 + 3 ^ 40 * 3921738 * 2
def baseEnd_3921738 : Nat := 671245531667427471913087

theorem tailTrace_3921738 : CollatzResearch.WordTrace tailWord_3921738 prefixEnd_3921738 671245531667427471913087 := by
  unfold tailWord_3921738
  simp only [CollatzResearch.WordTrace]
  refine ⟨35759383966555120092909467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95358357244146986914425245 35759383966555120092909467)
  ·
    refine ⟨53639075949832680139364201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35759383966555120092909467 53639075949832680139364201)
    ·
      refine ⟨40229306962374510104523151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53639075949832680139364201 40229306962374510104523151)
      ·
        refine ⟨60343960443561765156784727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40229306962374510104523151 60343960443561765156784727)
        ·
          refine ⟨90515940665342647735177091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60343960443561765156784727 90515940665342647735177091)
          ·
            refine ⟨135773910998013971602765637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90515940665342647735177091 135773910998013971602765637)
            ·
              refine ⟨25457608312127619675518557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135773910998013971602765637 25457608312127619675518557)
              ·
                refine ⟨9546603117047857378319459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25457608312127619675518557 9546603117047857378319459)
                ·
                  refine ⟨14319904675571786067479189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9546603117047857378319459 14319904675571786067479189)
                  ·
                    refine ⟨671245531667427471913087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14319904675571786067479189 671245531667427471913087)
                    ·
                      rfl

theorem cell23_3921738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_3921738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921738 prefixEnd_3921738 := by exact prefixLift 3921738
  have htrace : WordTrace (prefixWord ++ tailWord_3921738) baseStart_3921738 baseEnd_3921738 := by
    simpa [prefixWord, tailWord_3921738, baseEnd_3921738] using wordTrace_append hprefix tailTrace_3921738
  have hstable : (prefixWord ++ tailWord_3921738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921738).length < 2 ^ (prefixWord ++ tailWord_3921738).sum := by decide
  have hdescent : baseEnd_3921738 < baseStart_3921738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921745 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_3921745 : Nat := 118140960795 + 3921745 * 2 ^ 59
def prefixEnd_3921745 : Nat := 4983230072969 + 3 ^ 40 * 3921745 * 2
def baseEnd_3921745 : Nat := 2013740189366863888351729

theorem tailTrace_3921745 : CollatzResearch.WordTrace tailWord_3921745 prefixEnd_3921745 2013740189366863888351729 := by
  unfold tailWord_3921745
  simp only [CollatzResearch.WordTrace]
  refine ⟨143037791177195120567142689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95358527451463413711428459 143037791177195120567142689)
  ·
    refine ⟨107278343382896340425357017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143037791177195120567142689 107278343382896340425357017)
    ·
      refine ⟨80458757537172255319017763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107278343382896340425357017 80458757537172255319017763)
      ·
        refine ⟨120688136305758382978526645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80458757537172255319017763 120688136305758382978526645)
        ·
          refine ⟨11314512778664848404236873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120688136305758382978526645 11314512778664848404236873)
          ·
            refine ⟨8485884583998636303177655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11314512778664848404236873 8485884583998636303177655)
            ·
              refine ⟨12728826875997954454766483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485884583998636303177655 12728826875997954454766483)
              ·
                refine ⟨19093240313996931682149725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12728826875997954454766483 19093240313996931682149725)
                ·
                  refine ⟨7159965117748849380806147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19093240313996931682149725 7159965117748849380806147)
                  ·
                    refine ⟨10739947676623274071209221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7159965117748849380806147 10739947676623274071209221)
                    ·
                      refine ⟨2013740189366863888351729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10739947676623274071209221 2013740189366863888351729)
                      ·
                        rfl

theorem cell23_3921745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_3921745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921745 prefixEnd_3921745 := by exact prefixLift 3921745
  have htrace : WordTrace (prefixWord ++ tailWord_3921745) baseStart_3921745 baseEnd_3921745 := by
    simpa [prefixWord, tailWord_3921745, baseEnd_3921745] using wordTrace_append hprefix tailTrace_3921745
  have hstable : (prefixWord ++ tailWord_3921745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921745).length < 2 ^ (prefixWord ++ tailWord_3921745).sum := by decide
  have hdescent : baseEnd_3921745 < baseStart_3921745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921772 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 2, 4]
def baseStart_3921772 : Nat := 118140960795 + 3921772 * 2 ^ 59
def prefixEnd_3921772 : Nat := 4983230072969 + 3 ^ 40 * 3921772 * 2
def baseEnd_3921772 : Nat := 671251351114845094238035

theorem tailTrace_3921772 : CollatzResearch.WordTrace tailWord_3921772 prefixEnd_3921772 671251351114845094238035 := by
  unfold tailWord_3921772
  simp only [CollatzResearch.WordTrace]
  refine ⟨71519387974048652089187785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95359183965398202785583713 71519387974048652089187785)
  ·
    refine ⟨53639540980536489066890839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71519387974048652089187785 53639540980536489066890839)
    ·
      refine ⟨80459311470804733600336259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53639540980536489066890839 80459311470804733600336259)
      ·
        refine ⟨120688967206207100400504389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80459311470804733600336259 120688967206207100400504389)
        ·
          refine ⟨22629181351163831325094573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120688967206207100400504389 22629181351163831325094573)
          ·
            refine ⟨8485943006686436746910465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22629181351163831325094573 8485943006686436746910465)
            ·
              refine ⟨6364457255014827560182849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8485943006686436746910465 6364457255014827560182849)
              ·
                refine ⟨4773342941261120670137137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364457255014827560182849 4773342941261120670137137)
                ·
                  refine ⟨3580007205945840502602853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4773342941261120670137137 3580007205945840502602853)
                  ·
                    refine ⟨671251351114845094238035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580007205945840502602853 671251351114845094238035)
                    ·
                      rfl

theorem cell23_3921772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_3921772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921772 prefixEnd_3921772 := by exact prefixLift 3921772
  have htrace : WordTrace (prefixWord ++ tailWord_3921772) baseStart_3921772 baseEnd_3921772 := by
    simpa [prefixWord, tailWord_3921772, baseEnd_3921772] using wordTrace_append hprefix tailTrace_3921772
  have hstable : (prefixWord ++ tailWord_3921772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921772).length < 2 ^ (prefixWord ++ tailWord_3921772).sum := by decide
  have hdescent : baseEnd_3921772 < baseStart_3921772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921795 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 3]
def baseStart_3921795 : Nat := 118140960795 + 3921795 * 2 ^ 59
def prefixEnd_3921795 : Nat := 4983230072969 + 3 ^ 40 * 3921795 * 2
def baseEnd_3921795 : Nat := 2013765863399588692726499

theorem tailTrace_3921795 : CollatzResearch.WordTrace tailWord_3921795 prefixEnd_3921795 2013765863399588692726499 := by
  unfold tailWord_3921795
  simp only [CollatzResearch.WordTrace]
  refine ⟨143039614827013979106462839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95359743218009319404308559 143039614827013979106462839)
  ·
    refine ⟨214559422240520968659694259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143039614827013979106462839 214559422240520968659694259)
    ·
      refine ⟨321839133360781452989541389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214559422240520968659694259 321839133360781452989541389)
      ·
        refine ⟨120689675010293044871078021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321839133360781452989541389 120689675010293044871078021)
        ·
          refine ⟨22629314064429945913327129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120689675010293044871078021 22629314064429945913327129)
          ·
            refine ⟨16971985548322459434995347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22629314064429945913327129 16971985548322459434995347)
            ·
              refine ⟨25457978322483689152493021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16971985548322459434995347 25457978322483689152493021)
              ·
                refine ⟨9546741870931383432184883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25457978322483689152493021 9546741870931383432184883)
                ·
                  refine ⟨14320112806397075148277325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9546741870931383432184883 14320112806397075148277325)
                  ·
                    refine ⟨5370042302398903180603997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14320112806397075148277325 5370042302398903180603997)
                    ·
                      refine ⟨2013765863399588692726499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5370042302398903180603997 2013765863399588692726499)
                      ·
                        rfl

theorem cell23_3921795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_3921795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921795 prefixEnd_3921795 := by exact prefixLift 3921795
  have htrace : WordTrace (prefixWord ++ tailWord_3921795) baseStart_3921795 baseEnd_3921795 := by
    simpa [prefixWord, tailWord_3921795, baseEnd_3921795] using wordTrace_append hprefix tailTrace_3921795
  have hstable : (prefixWord ++ tailWord_3921795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921795).length < 2 ^ (prefixWord ++ tailWord_3921795).sum := by decide
  have hdescent : baseEnd_3921795 < baseStart_3921795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921802 : List Nat := [3, 1, 2, 4, 2, 1, 3, 7]
def baseStart_3921802 : Nat := 118140960795 + 3921802 * 2 ^ 59
def prefixEnd_3921802 : Nat := 4983230072969 + 3 ^ 40 * 3921802 * 2
def baseEnd_3921802 : Nat := 74584053991265561679221

theorem tailTrace_3921802 : CollatzResearch.WordTrace tailWord_3921802 prefixEnd_3921802 74584053991265561679221 := by
  unfold tailWord_3921802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35759967534497154825491915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95359913425325746201311773 35759967534497154825491915)
  ·
    refine ⟨53639951301745732238237873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35759967534497154825491915 53639951301745732238237873)
    ·
      refine ⟨40229963476309299178678405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53639951301745732238237873 40229963476309299178678405)
      ·
        refine ⟨7543118151807993596002201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40229963476309299178678405 7543118151807993596002201)
        ·
          refine ⟨5657338613855995197001651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7543118151807993596002201 5657338613855995197001651)
          ·
            refine ⟨8486007920783992795502477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657338613855995197001651 8486007920783992795502477)
            ·
              refine ⟨3182252970293997298313429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8486007920783992795502477 3182252970293997298313429)
              ·
                refine ⟨74584053991265561679221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3182252970293997298313429 74584053991265561679221)
                ·
                  rfl

theorem cell23_3921802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 7].length) (baseStart_3921802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921802 prefixEnd_3921802 := by exact prefixLift 3921802
  have htrace : WordTrace (prefixWord ++ tailWord_3921802) baseStart_3921802 baseEnd_3921802 := by
    simpa [prefixWord, tailWord_3921802, baseEnd_3921802] using wordTrace_append hprefix tailTrace_3921802
  have hstable : (prefixWord ++ tailWord_3921802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921802).length < 2 ^ (prefixWord ++ tailWord_3921802).sum := by decide
  have hdescent : baseEnd_3921802 < baseStart_3921802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921812 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3921812 : Nat := 118140960795 + 3921812 * 2 ^ 59
def prefixEnd_3921812 : Nat := 4983230072969 + 3 ^ 40 * 3921812 * 2
def baseEnd_3921812 : Nat := 2013774592570715126213921

theorem tailTrace_3921812 : CollatzResearch.WordTrace tailWord_3921812 prefixEnd_3921812 2013774592570715126213921 := by
  unfold tailWord_3921812
  simp only [CollatzResearch.WordTrace]
  refine ⟨71520117433976195504915845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95360156578634927339887793 71520117433976195504915845)
  ·
    refine ⟨13410022018870536657171721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71520117433976195504915845 13410022018870536657171721)
    ·
      refine ⟨10057516514152902492878791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13410022018870536657171721 10057516514152902492878791)
      ·
        refine ⟨15086274771229353739318187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057516514152902492878791 15086274771229353739318187)
        ·
          refine ⟨22629412156844030608977281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15086274771229353739318187 22629412156844030608977281)
          ·
            refine ⟨16972059117633022956732961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22629412156844030608977281 16972059117633022956732961)
            ·
              refine ⟨12729044338224767217549721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16972059117633022956732961 12729044338224767217549721)
              ·
                refine ⟨9546783253668575413162291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12729044338224767217549721 9546783253668575413162291)
                ·
                  refine ⟨14320174880502863119743437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9546783253668575413162291 14320174880502863119743437)
                  ·
                    refine ⟨5370065580188573669903789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14320174880502863119743437 5370065580188573669903789)
                    ·
                      refine ⟨2013774592570715126213921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5370065580188573669903789 2013774592570715126213921)
                      ·
                        rfl

theorem cell23_3921812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3921812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921812 prefixEnd_3921812 := by exact prefixLift 3921812
  have htrace : WordTrace (prefixWord ++ tailWord_3921812) baseStart_3921812 baseEnd_3921812 := by
    simpa [prefixWord, tailWord_3921812, baseEnd_3921812] using wordTrace_append hprefix tailTrace_3921812
  have hstable : (prefixWord ++ tailWord_3921812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921812).length < 2 ^ (prefixWord ++ tailWord_3921812).sum := by decide
  have hdescent : baseEnd_3921812 < baseStart_3921812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921845 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3921845 : Nat := 118140960795 + 3921845 * 2 ^ 59
def prefixEnd_3921845 : Nat := 4983230072969 + 3 ^ 40 * 3921845 * 2
def baseEnd_3921845 : Nat := 671263845810771165700423

theorem tailTrace_3921845 : CollatzResearch.WordTrace tailWord_3921845 prefixEnd_3921845 671263845810771165700423 := by
  unfold tailWord_3921845
  simp only [CollatzResearch.WordTrace]
  refine ⟨143041438476832837645782989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95360958984555225097188659 143041438476832837645782989)
  ·
    refine ⟨53640539428812314117168621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143041438476832837645782989 53640539428812314117168621)
    ·
      refine ⟨20115202285804617793938233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53640539428812314117168621 20115202285804617793938233)
      ·
        refine ⟨15086401714353463345453675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20115202285804617793938233 15086401714353463345453675)
        ·
          refine ⟨22629602571530195018180513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15086401714353463345453675 22629602571530195018180513)
          ·
            refine ⟨16972201928647646263635385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22629602571530195018180513 16972201928647646263635385)
            ·
              refine ⟨12729151446485734697726539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16972201928647646263635385 12729151446485734697726539)
              ·
                refine ⟨19093727169728602046589809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12729151446485734697726539 19093727169728602046589809)
                ·
                  refine ⟨14320295377296451534942357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19093727169728602046589809 14320295377296451534942357)
                  ·
                    refine ⟨671263845810771165700423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14320295377296451534942357 671263845810771165700423)
                    ·
                      rfl

theorem cell23_3921845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3921845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921845 prefixEnd_3921845 := by exact prefixLift 3921845
  have htrace : WordTrace (prefixWord ++ tailWord_3921845) baseStart_3921845 baseEnd_3921845 := by
    simpa [prefixWord, tailWord_3921845, baseEnd_3921845] using wordTrace_append hprefix tailTrace_3921845
  have hstable : (prefixWord ++ tailWord_3921845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921845).length < 2 ^ (prefixWord ++ tailWord_3921845).sum := by decide
  have hdescent : baseEnd_3921845 < baseStart_3921845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921943 : List Nat := [1, 1, 3, 5, 3, 1, 2, 2, 5]
def baseStart_3921943 : Nat := 118140960795 + 3921943 * 2 ^ 59
def prefixEnd_3921943 : Nat := 4983230072969 + 3 ^ 40 * 3921943 * 2
def baseEnd_3921943 : Nat := 223760206504050457075091

theorem tailTrace_3921943 : CollatzResearch.WordTrace tailWord_3921943 prefixEnd_3921943 223760206504050457075091 := by
  unfold tailWord_3921943
  simp only [CollatzResearch.WordTrace]
  refine ⟨143045012830477800382850483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95363341886985200255233655 143045012830477800382850483)
  ·
    refine ⟨214567519245716700574275725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143045012830477800382850483 214567519245716700574275725)
    ·
      refine ⟨80462819717143762715353397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214567519245716700574275725 80462819717143762715353397)
      ·
        refine ⟨7543389348482227754564381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80462819717143762715353397 7543389348482227754564381)
        ·
          refine ⟨2828771005680835407961643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7543389348482227754564381 2828771005680835407961643)
          ·
            refine ⟨4243156508521253111942465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828771005680835407961643 4243156508521253111942465)
            ·
              refine ⟨3182367381390939833956849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4243156508521253111942465 3182367381390939833956849)
              ·
                refine ⟨2386775536043204875467637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182367381390939833956849 2386775536043204875467637)
                ·
                  refine ⟨223760206504050457075091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386775536043204875467637 223760206504050457075091)
                  ·
                    rfl

theorem cell23_3921943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 5].length) (baseStart_3921943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921943 prefixEnd_3921943 := by exact prefixLift 3921943
  have htrace : WordTrace (prefixWord ++ tailWord_3921943) baseStart_3921943 baseEnd_3921943 := by
    simpa [prefixWord, tailWord_3921943, baseEnd_3921943] using wordTrace_append hprefix tailTrace_3921943
  have hstable : (prefixWord ++ tailWord_3921943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921943).length < 2 ^ (prefixWord ++ tailWord_3921943).sum := by decide
  have hdescent : baseEnd_3921943 < baseStart_3921943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921945 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 3]
def baseStart_3921945 : Nat := 118140960795 + 3921945 * 2 ^ 59
def prefixEnd_3921945 : Nat := 4983230072969 + 3 ^ 40 * 3921945 * 2
def baseEnd_3921945 : Nat := 2013842885497763105850809

theorem tailTrace_3921945 : CollatzResearch.WordTrace tailWord_3921945 prefixEnd_3921945 2013842885497763105850809 := by
  unfold tailWord_3921945
  simp only [CollatzResearch.WordTrace]
  refine ⟨143045085776470554724423289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95363390517647036482948859 143045085776470554724423289)
  ·
    refine ⟨107283814332352916043317467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143045085776470554724423289 107283814332352916043317467)
    ·
      refine ⟨160925721498529374064976201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107283814332352916043317467 160925721498529374064976201)
      ·
        refine ⟨120694291123897030548732151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160925721498529374064976201 120694291123897030548732151)
        ·
          refine ⟨181041436685845545823098227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120694291123897030548732151 181041436685845545823098227)
          ·
            refine ⟨271562155028768318734647341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181041436685845545823098227 271562155028768318734647341)
            ·
              refine ⟨101835808135788119525492753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271562155028768318734647341 101835808135788119525492753)
              ·
                refine ⟨76376856101841089644119565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101835808135788119525492753 76376856101841089644119565)
                ·
                  refine ⟨28641321038190408616544837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76376856101841089644119565 28641321038190408616544837)
                  ·
                    refine ⟨5370247694660701615602157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28641321038190408616544837 5370247694660701615602157)
                    ·
                      refine ⟨2013842885497763105850809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5370247694660701615602157 2013842885497763105850809)
                      ·
                        rfl

theorem cell23_3921945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_3921945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921945 prefixEnd_3921945 := by exact prefixLift 3921945
  have htrace : WordTrace (prefixWord ++ tailWord_3921945) baseStart_3921945 baseEnd_3921945 := by
    simpa [prefixWord, tailWord_3921945, baseEnd_3921945] using wordTrace_append hprefix tailTrace_3921945
  have hstable : (prefixWord ++ tailWord_3921945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921945).length < 2 ^ (prefixWord ++ tailWord_3921945).sum := by decide
  have hdescent : baseEnd_3921945 < baseStart_3921945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3921976 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 2, 1, 4]
def baseStart_3921976 : Nat := 118140960795 + 3921976 * 2 ^ 59
def prefixEnd_3921976 : Nat := 4983230072969 + 3 ^ 40 * 3921976 * 2
def baseEnd_3921976 : Nat := 2013858803398052484563167

theorem tailTrace_3921976 : CollatzResearch.WordTrace tailWord_3921976 prefixEnd_3921976 2013858803398052484563167 := by
  unfold tailWord_3921976
  simp only [CollatzResearch.WordTrace]
  refine ⟨71523108219679123509400891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95364144292905498012534521 71523108219679123509400891)
  ·
    refine ⟨107284662329518685264101337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71523108219679123509400891 107284662329518685264101337)
    ·
      refine ⟨80463496747139013948076003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107284662329518685264101337 80463496747139013948076003)
      ·
        refine ⟨120695245120708520922114005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80463496747139013948076003 120695245120708520922114005)
        ·
          refine ⟨2828794807516605959112047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 120695245120708520922114005 2828794807516605959112047)
          ·
            refine ⟨4243192211274908938668071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828794807516605959112047 4243192211274908938668071)
            ·
              refine ⟨6364788316912363408002107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243192211274908938668071 6364788316912363408002107)
              ·
                refine ⟨9547182475368545112003161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364788316912363408002107 9547182475368545112003161)
                ·
                  refine ⟨7160386856526408834002371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9547182475368545112003161 7160386856526408834002371)
                  ·
                    refine ⟨10740580284789613251003557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7160386856526408834002371 10740580284789613251003557)
                    ·
                      refine ⟨2013858803398052484563167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10740580284789613251003557 2013858803398052484563167)
                      ·
                        rfl

theorem cell23_3921976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_3921976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3921976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3921976 prefixEnd_3921976 := by exact prefixLift 3921976
  have htrace : WordTrace (prefixWord ++ tailWord_3921976) baseStart_3921976 baseEnd_3921976 := by
    simpa [prefixWord, tailWord_3921976, baseEnd_3921976] using wordTrace_append hprefix tailTrace_3921976
  have hstable : (prefixWord ++ tailWord_3921976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3921976).length < 2 ^ (prefixWord ++ tailWord_3921976).sum := by decide
  have hdescent : baseEnd_3921976 < baseStart_3921976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3921976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922009 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 3]
def baseStart_3922009 : Nat := 118140960795 + 3922009 * 2 ^ 59
def prefixEnd_3922009 : Nat := 4983230072969 + 3 ^ 40 * 3922009 * 2
def baseEnd_3922009 : Nat := 2013875748259650855450515

theorem tailTrace_3922009 : CollatzResearch.WordTrace tailWord_3922009 prefixEnd_3922009 2013875748259650855450515 := by
  unfold tailWord_3922009
  simp only [CollatzResearch.WordTrace]
  refine ⟨143047420048238693654753081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95364946698825795769835387 143047420048238693654753081)
  ·
    refine ⟨107285565036179020241064811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143047420048238693654753081 107285565036179020241064811)
    ·
      refine ⟨160928347554268530361597217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107285565036179020241064811 160928347554268530361597217)
      ·
        refine ⟨120696260665701397771197913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160928347554268530361597217 120696260665701397771197913)
        ·
          refine ⟨90522195499276048328398435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120696260665701397771197913 90522195499276048328398435)
          ·
            refine ⟨135783293248914072492597653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90522195499276048328398435 135783293248914072492597653)
            ·
              refine ⟨6364841871042847148090515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135783293248914072492597653 6364841871042847148090515)
              ·
                refine ⟨9547262806564270722135773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364841871042847148090515 9547262806564270722135773)
                ·
                  refine ⟨3580223552461601520800915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9547262806564270722135773 3580223552461601520800915)
                  ·
                    refine ⟨5370335328692402281201373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3580223552461601520800915 5370335328692402281201373)
                    ·
                      refine ⟨2013875748259650855450515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5370335328692402281201373 2013875748259650855450515)
                      ·
                        rfl

theorem cell23_3922009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_3922009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922009 prefixEnd_3922009 := by exact prefixLift 3922009
  have htrace : WordTrace (prefixWord ++ tailWord_3922009) baseStart_3922009 baseEnd_3922009 := by
    simpa [prefixWord, tailWord_3922009, baseEnd_3922009] using wordTrace_append hprefix tailTrace_3922009
  have hstable : (prefixWord ++ tailWord_3922009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922009).length < 2 ^ (prefixWord ++ tailWord_3922009).sum := by decide
  have hdescent : baseEnd_3922009 < baseStart_3922009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922015 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 4]
def baseStart_3922015 : Nat := 118140960795 + 3922015 * 2 ^ 59
def prefixEnd_3922015 : Nat := 4983230072969 + 3 ^ 40 * 3922015 * 2
def baseEnd_3922015 : Nat := 2013878829143577831975487

theorem tailTrace_3922015 : CollatzResearch.WordTrace tailWord_3922015 prefixEnd_3922015 2013878829143577831975487 := by
  unfold tailWord_3922015
  simp only [CollatzResearch.WordTrace]
  refine ⟨143047638886216956679471499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95365092590811304452980999 143047638886216956679471499)
  ·
    refine ⟨214571458329325435019207249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143047638886216956679471499 214571458329325435019207249)
    ·
      refine ⟨160928593746994076264405437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214571458329325435019207249 160928593746994076264405437)
      ·
        refine ⟨60348222655122778599152039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160928593746994076264405437 60348222655122778599152039)
        ·
          refine ⟨90522333982684167898728059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60348222655122778599152039 90522333982684167898728059)
          ·
            refine ⟨135783500974026251848092089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90522333982684167898728059 135783500974026251848092089)
            ·
              refine ⟨101837625730519688886069067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135783500974026251848092089 101837625730519688886069067)
              ·
                refine ⟨152756438595779533329103601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101837625730519688886069067 152756438595779533329103601)
                ·
                  refine ⟨114567328946834649996827701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152756438595779533329103601 114567328946834649996827701)
                  ·
                    refine ⟨10740687088765748437202597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114567328946834649996827701 10740687088765748437202597)
                    ·
                      refine ⟨2013878829143577831975487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10740687088765748437202597 2013878829143577831975487)
                      ·
                        rfl

theorem cell23_3922015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_3922015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922015 prefixEnd_3922015 := by exact prefixLift 3922015
  have htrace : WordTrace (prefixWord ++ tailWord_3922015) baseStart_3922015 baseEnd_3922015 := by
    simpa [prefixWord, tailWord_3922015, baseEnd_3922015] using wordTrace_append hprefix tailTrace_3922015
  have hstable : (prefixWord ++ tailWord_3922015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922015).length < 2 ^ (prefixWord ++ tailWord_3922015).sum := by decide
  have hdescent : baseEnd_3922015 < baseStart_3922015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922029 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_3922029 : Nat := 118140960795 + 3922029 * 2 ^ 59
def prefixEnd_3922029 : Nat := 4983230072969 + 3 ^ 40 * 3922029 * 2
def baseEnd_3922029 : Nat := 671295339290913592400141

theorem tailTrace_3922029 : CollatzResearch.WordTrace tailWord_3922029 prefixEnd_3922029 671295339290913592400141 := by
  unfold tailWord_3922029
  simp only [CollatzResearch.WordTrace]
  refine ⟨143048149508166237070481141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95365433005444158046987427 143048149508166237070481141)
  ·
    refine ⟨13410764016390584725357607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143048149508166237070481141 13410764016390584725357607)
    ·
      refine ⟨20116146024585877088036411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13410764016390584725357607 20116146024585877088036411)
      ·
        refine ⟨30174219036878815632054617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20116146024585877088036411 30174219036878815632054617)
        ·
          refine ⟨22630664277659111724040963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30174219036878815632054617 22630664277659111724040963)
          ·
            refine ⟨33945996416488667586061445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22630664277659111724040963 33945996416488667586061445)
            ·
              refine ⟨6364874328091625172386521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33945996416488667586061445 6364874328091625172386521)
              ·
                refine ⟨4773655746068718879289891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364874328091625172386521 4773655746068718879289891)
                ·
                  refine ⟨7160483619103078318934837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4773655746068718879289891 7160483619103078318934837)
                  ·
                    refine ⟨671295339290913592400141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7160483619103078318934837 671295339290913592400141)
                    ·
                      rfl

theorem cell23_3922029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_3922029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922029 prefixEnd_3922029 := by exact prefixLift 3922029
  have htrace : WordTrace (prefixWord ++ tailWord_3922029) baseStart_3922029 baseEnd_3922029 := by
    simpa [prefixWord, tailWord_3922029, baseEnd_3922029] using wordTrace_append hprefix tailTrace_3922029
  have hstable : (prefixWord ++ tailWord_3922029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922029).length < 2 ^ (prefixWord ++ tailWord_3922029).sum := by decide
  have hdescent : baseEnd_3922029 < baseStart_3922029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922055 : List Nat := [1, 1, 4, 2, 1, 1, 13]
def baseStart_3922055 : Nat := 118140960795 + 3922055 * 2 ^ 59
def prefixEnd_3922055 : Nat := 4983230072969 + 3 ^ 40 * 3922055 * 2
def baseEnd_3922055 : Nat := 24862955165058736734263

theorem tailTrace_3922055 : CollatzResearch.WordTrace tailWord_3922055 prefixEnd_3922055 24862955165058736734263 := by
  unfold tailWord_3922055
  simp only [CollatzResearch.WordTrace]
  refine ⟨143049097806072043510927619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95366065204048029007285079 143049097806072043510927619)
  ·
    refine ⟨214573646709108065266391429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143049097806072043510927619 214573646709108065266391429)
    ·
      refine ⟨40232558757957762237448393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214573646709108065266391429 40232558757957762237448393)
      ·
        refine ⟨30174419068468321678086295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40232558757957762237448393 30174419068468321678086295)
        ·
          refine ⟨45261628602702482517129443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30174419068468321678086295 45261628602702482517129443)
          ·
            refine ⟨67892442904053723775694165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45261628602702482517129443 67892442904053723775694165)
            ·
              refine ⟨24862955165058736734263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 67892442904053723775694165 24862955165058736734263)
              ·
                rfl

theorem cell23_3922055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 13].length) (baseStart_3922055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922055 prefixEnd_3922055 := by exact prefixLift 3922055
  have htrace : WordTrace (prefixWord ++ tailWord_3922055) baseStart_3922055 baseEnd_3922055 := by
    simpa [prefixWord, tailWord_3922055, baseEnd_3922055] using wordTrace_append hprefix tailTrace_3922055
  have hstable : (prefixWord ++ tailWord_3922055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922055).length < 2 ^ (prefixWord ++ tailWord_3922055).sum := by decide
  have hdescent : baseEnd_3922055 < baseStart_3922055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922075 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6]
def baseStart_3922075 : Nat := 118140960795 + 3922075 * 2 ^ 59
def prefixEnd_3922075 : Nat := 4983230072969 + 3 ^ 40 * 3922075 * 2
def baseEnd_3922075 : Nat := 2013909637982847597225211

theorem tailTrace_3922075 : CollatzResearch.WordTrace tailWord_3922075 prefixEnd_3922075 2013909637982847597225211 := by
  unfold tailWord_3922075
  simp only [CollatzResearch.WordTrace]
  refine ⟨143049827265999586926655679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95366551510666391284437119 143049827265999586926655679)
  ·
    refine ⟨214574740898999380389983519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143049827265999586926655679 214574740898999380389983519)
    ·
      refine ⟨321862111348499070584975279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214574740898999380389983519 321862111348499070584975279)
      ·
        refine ⟨482793167022748605877462919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321862111348499070584975279 482793167022748605877462919)
        ·
          refine ⟨724189750534122908816194379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482793167022748605877462919 724189750534122908816194379)
          ·
            refine ⟨1086284625801184363224291569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724189750534122908816194379 1086284625801184363224291569)
            ·
              refine ⟨814713469350888272418218677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1086284625801184363224291569 814713469350888272418218677)
              ·
                refine ⟨76379387751645775539208001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 814713469350888272418218677 76379387751645775539208001)
                ·
                  refine ⟨57284540813734331654406001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76379387751645775539208001 57284540813734331654406001)
                  ·
                    refine ⟨42963405610300748740804501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57284540813734331654406001 42963405610300748740804501)
                    ·
                      refine ⟨2013909637982847597225211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42963405610300748740804501 2013909637982847597225211)
                      ·
                        rfl

theorem cell23_3922075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_3922075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922075 prefixEnd_3922075 := by exact prefixLift 3922075
  have htrace : WordTrace (prefixWord ++ tailWord_3922075) baseStart_3922075 baseEnd_3922075 := by
    simpa [prefixWord, tailWord_3922075, baseEnd_3922075] using wordTrace_append hprefix tailTrace_3922075
  have hstable : (prefixWord ++ tailWord_3922075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922075).length < 2 ^ (prefixWord ++ tailWord_3922075).sum := by decide
  have hdescent : baseEnd_3922075 < baseStart_3922075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922122 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_3922122 : Nat := 118140960795 + 3922122 * 2 ^ 59
def prefixEnd_3922122 : Nat := 4983230072969 + 3 ^ 40 * 3922122 * 2
def baseEnd_3922122 : Nat := 2013933771573608913337495

theorem tailTrace_3922122 : CollatzResearch.WordTrace tailWord_3922122 prefixEnd_3922122 2013933771573608913337495 := by
  unfold tailWord_3922122
  simp only [CollatzResearch.WordTrace]
  refine ⟨35762885374207328488404155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95367694331219542635744413 35762885374207328488404155)
  ·
    refine ⟨53644328061310992732606233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35762885374207328488404155 53644328061310992732606233)
    ·
      refine ⟨40233246045983244549454675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53644328061310992732606233 40233246045983244549454675)
      ·
        refine ⟨60349869068974866824182013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40233246045983244549454675 60349869068974866824182013)
        ·
          refine ⟨22631200900865575059068255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60349869068974866824182013 22631200900865575059068255)
          ·
            refine ⟨33946801351298362588602383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22631200900865575059068255 33946801351298362588602383)
            ·
              refine ⟨50920202026947543882903575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33946801351298362588602383 50920202026947543882903575)
              ·
                refine ⟨76380303040421315824355363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50920202026947543882903575 76380303040421315824355363)
                ·
                  refine ⟨114570454560631973736533045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76380303040421315824355363 114570454560631973736533045)
                  ·
                    refine ⟨10740980115059247537799973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114570454560631973736533045 10740980115059247537799973)
                    ·
                      refine ⟨2013933771573608913337495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10740980115059247537799973 2013933771573608913337495)
                      ·
                        rfl

theorem cell23_3922122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_3922122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922122 prefixEnd_3922122 := by exact prefixLift 3922122
  have htrace : WordTrace (prefixWord ++ tailWord_3922122) baseStart_3922122 baseEnd_3922122 := by
    simpa [prefixWord, tailWord_3922122, baseEnd_3922122] using wordTrace_append hprefix tailTrace_3922122
  have hstable : (prefixWord ++ tailWord_3922122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922122).length < 2 ^ (prefixWord ++ tailWord_3922122).sum := by decide
  have hdescent : baseEnd_3922122 < baseStart_3922122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922126 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_3922126 : Nat := 118140960795 + 3922126 * 2 ^ 59
def prefixEnd_3922126 : Nat := 4983230072969 + 3 ^ 40 * 3922126 * 2
def baseEnd_3922126 : Nat := 2013935825496226897687477

theorem tailTrace_3922126 : CollatzResearch.WordTrace tailWord_3922126 prefixEnd_3922126 2013935825496226897687477 := by
  unfold tailWord_3922126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881460923601852829595279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95367791592543215091174821 17881460923601852829595279)
  ·
    refine ⟨26822191385402779244392919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17881460923601852829595279 26822191385402779244392919)
    ·
      refine ⟨40233287078104168866589379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26822191385402779244392919 40233287078104168866589379)
      ·
        refine ⟨60349930617156253299884069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40233287078104168866589379 60349930617156253299884069)
        ·
          refine ⟨11315611990716797493728263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60349930617156253299884069 11315611990716797493728263)
          ·
            refine ⟨16973417986075196240592395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11315611990716797493728263 16973417986075196240592395)
            ·
              refine ⟨25460126979112794360888593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16973417986075196240592395 25460126979112794360888593)
              ·
                refine ⟨19095095234334595770666445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25460126979112794360888593 19095095234334595770666445)
                ·
                  refine ⟨7160660712875473413999917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19095095234334595770666445 7160660712875473413999917)
                  ·
                    refine ⟨2685247767328302530249969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7160660712875473413999917 2685247767328302530249969)
                    ·
                      refine ⟨2013935825496226897687477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685247767328302530249969 2013935825496226897687477)
                      ·
                        rfl

theorem cell23_3922126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_3922126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922126 prefixEnd_3922126 := by exact prefixLift 3922126
  have htrace : WordTrace (prefixWord ++ tailWord_3922126) baseStart_3922126 baseEnd_3922126 := by
    simpa [prefixWord, tailWord_3922126, baseEnd_3922126] using wordTrace_append hprefix tailTrace_3922126
  have hstable : (prefixWord ++ tailWord_3922126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922126).length < 2 ^ (prefixWord ++ tailWord_3922126).sum := by decide
  have hdescent : baseEnd_3922126 < baseStart_3922126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922139 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 1, 4, 2]
def baseStart_3922139 : Nat := 118140960795 + 3922139 * 2 ^ 59
def prefixEnd_3922139 : Nat := 4983230072969 + 3 ^ 40 * 3922139 * 2
def baseEnd_3922139 : Nat := 2013942500744735346824917

theorem tailTrace_3922139 : CollatzResearch.WordTrace tailWord_3922139 prefixEnd_3922139 2013942500744735346824917 := by
  unfold tailWord_3922139
  simp only [CollatzResearch.WordTrace]
  refine ⟨143052161537767725856985471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95368107691845150571323647 143052161537767725856985471)
  ·
    refine ⟨214578242306651588785478207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143052161537767725856985471 214578242306651588785478207)
    ·
      refine ⟨321867363459977383178217311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214578242306651588785478207 321867363459977383178217311)
      ·
        refine ⟨482801045189966074767325967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321867363459977383178217311 482801045189966074767325967)
        ·
          refine ⟨724201567784949112150988951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482801045189966074767325967 724201567784949112150988951)
          ·
            refine ⟨1086302351677423668226483427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724201567784949112150988951 1086302351677423668226483427)
            ·
              refine ⟨1629453527516135502339725141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086302351677423668226483427 1629453527516135502339725141)
              ·
                refine ⟨9547579262789856459021827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1629453527516135502339725141 9547579262789856459021827)
                ·
                  refine ⟨14321368894184784688532741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9547579262789856459021827 14321368894184784688532741)
                  ·
                    refine ⟨2685256667659647129099889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14321368894184784688532741 2685256667659647129099889)
                    ·
                      refine ⟨2013942500744735346824917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685256667659647129099889 2013942500744735346824917)
                      ·
                        rfl

theorem cell23_3922139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 4, 2].length) (baseStart_3922139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922139 prefixEnd_3922139 := by exact prefixLift 3922139
  have htrace : WordTrace (prefixWord ++ tailWord_3922139) baseStart_3922139 baseEnd_3922139 := by
    simpa [prefixWord, tailWord_3922139, baseEnd_3922139] using wordTrace_append hprefix tailTrace_3922139
  have hstable : (prefixWord ++ tailWord_3922139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922139).length < 2 ^ (prefixWord ++ tailWord_3922139).sum := by decide
  have hdescent : baseEnd_3922139 < baseStart_3922139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922156 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 4, 2, 2]
def baseStart_3922156 : Nat := 118140960795 + 3922156 * 2 ^ 59
def prefixEnd_3922156 : Nat := 4983230072969 + 3 ^ 40 * 3922156 * 2
def baseEnd_3922156 : Nat := 2013951229915861780312339

theorem tailTrace_3922156 : CollatzResearch.WordTrace tailWord_3922156 prefixEnd_3922156 2013951229915861780312339 := by
  unfold tailWord_3922156
  simp only [CollatzResearch.WordTrace]
  refine ⟨71526390789353068880177161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95368521052470758506902881 71526390789353068880177161)
  ·
    refine ⟨53644793092014801660132871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71526390789353068880177161 53644793092014801660132871)
    ·
      refine ⟨80467189638022202490199307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53644793092014801660132871 80467189638022202490199307)
      ·
        refine ⟨120700784457033303735298961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80467189638022202490199307 120700784457033303735298961)
        ·
          refine ⟨90525588342774977801474221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120700784457033303735298961 90525588342774977801474221)
          ·
            refine ⟨33947095628540616675552833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90525588342774977801474221 33947095628540616675552833)
            ·
              refine ⟨25460321721405462506664625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33947095628540616675552833 25460321721405462506664625)
              ·
                refine ⟨19095241291054096879998469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25460321721405462506664625 19095241291054096879998469)
                ·
                  refine ⟨3580357742072643164999713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19095241291054096879998469 3580357742072643164999713)
                  ·
                    refine ⟨2685268306554482373749785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3580357742072643164999713 2685268306554482373749785)
                    ·
                      refine ⟨2013951229915861780312339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685268306554482373749785 2013951229915861780312339)
                      ·
                        rfl

theorem cell23_3922156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_3922156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922156 prefixEnd_3922156 := by exact prefixLift 3922156
  have htrace : WordTrace (prefixWord ++ tailWord_3922156) baseStart_3922156 baseEnd_3922156 := by
    simpa [prefixWord, tailWord_3922156, baseEnd_3922156] using wordTrace_append hprefix tailTrace_3922156
  have hstable : (prefixWord ++ tailWord_3922156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922156).length < 2 ^ (prefixWord ++ tailWord_3922156).sum := by decide
  have hdescent : baseEnd_3922156 < baseStart_3922156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922179 : List Nat := [1, 1, 1, 3, 2, 3, 1, 6, 5]
def baseStart_3922179 : Nat := 118140960795 + 3922179 * 2 ^ 59
def prefixEnd_3922179 : Nat := 4983230072969 + 3 ^ 40 * 3922179 * 2
def baseEnd_3922179 : Nat := 223773671107879465591637

theorem tailTrace_3922179 : CollatzResearch.WordTrace tailWord_3922179 prefixEnd_3922179 223773671107879465591637 := by
  unfold tailWord_3922179
  simp only [CollatzResearch.WordTrace]
  refine ⟨143053620457622812688441591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95369080305081875125627727 143053620457622812688441591)
  ·
    refine ⟨214580430686434219032662387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143053620457622812688441591 214580430686434219032662387)
    ·
      refine ⟨321870646029651328548993581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214580430686434219032662387 321870646029651328548993581)
      ·
        refine ⟨120701492261119248205872593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321870646029651328548993581 120701492261119248205872593)
        ·
          refine ⟨90526119195839436154404445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120701492261119248205872593 90526119195839436154404445)
          ·
            refine ⟨33947294698439788557901667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90526119195839436154404445 33947294698439788557901667)
            ·
              refine ⟨50920942047659682836852501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33947294698439788557901667 50920942047659682836852501)
              ·
                refine ⟨2386919158484047632977461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50920942047659682836852501 2386919158484047632977461)
                ·
                  refine ⟨223773671107879465591637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386919158484047632977461 223773671107879465591637)
                  ·
                    rfl

theorem cell23_3922179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 5].length) (baseStart_3922179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922179 prefixEnd_3922179 := by exact prefixLift 3922179
  have htrace : WordTrace (prefixWord ++ tailWord_3922179) baseStart_3922179 baseEnd_3922179 := by
    simpa [prefixWord, tailWord_3922179, baseEnd_3922179] using wordTrace_append hprefix tailTrace_3922179
  have hstable : (prefixWord ++ tailWord_3922179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922179).length < 2 ^ (prefixWord ++ tailWord_3922179).sum := by decide
  have hdescent : baseEnd_3922179 < baseStart_3922179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922190 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_3922190 : Nat := 118140960795 + 3922190 * 2 ^ 59
def prefixEnd_3922190 : Nat := 4983230072969 + 3 ^ 40 * 3922190 * 2
def baseEnd_3922190 : Nat := 2013968688258114647287183

theorem tailTrace_3922190 : CollatzResearch.WordTrace tailWord_3922190 prefixEnd_3922190 2013968688258114647287183 := by
  unfold tailWord_3922190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881752707572870195886503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95369347773721974378061349 17881752707572870195886503)
  ·
    refine ⟨26822629061359305293829755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17881752707572870195886503 26822629061359305293829755)
    ·
      refine ⟨40233943592038957940744633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26822629061359305293829755 40233943592038957940744633)
      ·
        refine ⟨30175457694029218455558475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40233943592038957940744633 30175457694029218455558475)
        ·
          refine ⟨45263186541043827683337713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30175457694029218455558475 45263186541043827683337713)
          ·
            refine ⟨33947389905782870762503285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45263186541043827683337713 33947389905782870762503285)
            ·
              refine ⟨3182567803667144133984683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33947389905782870762503285 3182567803667144133984683)
              ·
                refine ⟨4773851705500716200977025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182567803667144133984683 4773851705500716200977025)
                ·
                  refine ⟨3580388779125537150732769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4773851705500716200977025 3580388779125537150732769)
                  ·
                    refine ⟨2685291584344152863049577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3580388779125537150732769 2685291584344152863049577)
                    ·
                      refine ⟨2013968688258114647287183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685291584344152863049577 2013968688258114647287183)
                      ·
                        rfl

theorem cell23_3922190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_3922190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922190 prefixEnd_3922190 := by exact prefixLift 3922190
  have htrace : WordTrace (prefixWord ++ tailWord_3922190) baseStart_3922190 baseEnd_3922190 := by
    simpa [prefixWord, tailWord_3922190, baseEnd_3922190] using wordTrace_append hprefix tailTrace_3922190
  have hstable : (prefixWord ++ tailWord_3922190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922190).length < 2 ^ (prefixWord ++ tailWord_3922190).sum := by decide
  have hdescent : baseEnd_3922190 < baseStart_3922190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922213 : List Nat := [1, 3, 1, 2, 5, 2, 1, 3, 5]
def baseStart_3922213 : Nat := 118140960795 + 3922213 * 2 ^ 59
def prefixEnd_3922213 : Nat := 4983230072969 + 3 ^ 40 * 3922213 * 2
def baseEnd_3922213 : Nat := 223775610923685339699953

theorem tailTrace_3922213 : CollatzResearch.WordTrace tailWord_3922213 prefixEnd_3922213 223775610923685339699953 := by
  unfold tailWord_3922213
  simp only [CollatzResearch.WordTrace]
  refine ⟨143054860539499636495179293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95369907026333090996786195 143054860539499636495179293)
  ·
    refine ⟨53645572702312363685692235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143054860539499636495179293 53645572702312363685692235)
    ·
      refine ⟨80468359053468545528538353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53645572702312363685692235 80468359053468545528538353)
      ·
        refine ⟨60351269290101409146403765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80468359053468545528538353 60351269290101409146403765)
        ·
          refine ⟨5657931495947007107475353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60351269290101409146403765 5657931495947007107475353)
          ·
            refine ⟨4243448621960255330606515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657931495947007107475353 4243448621960255330606515)
            ·
              refine ⟨6365172932940382995909773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4243448621960255330606515 6365172932940382995909773)
              ·
                refine ⟨2386939849852643623466165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6365172932940382995909773 2386939849852643623466165)
                ·
                  refine ⟨223775610923685339699953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386939849852643623466165 223775610923685339699953)
                  ·
                    rfl

theorem cell23_3922213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_3922213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922213 prefixEnd_3922213 := by exact prefixLift 3922213
  have htrace : WordTrace (prefixWord ++ tailWord_3922213) baseStart_3922213 baseEnd_3922213 := by
    simpa [prefixWord, tailWord_3922213, baseEnd_3922213] using wordTrace_append hprefix tailTrace_3922213
  have hstable : (prefixWord ++ tailWord_3922213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922213).length < 2 ^ (prefixWord ++ tailWord_3922213).sum := by decide
  have hdescent : baseEnd_3922213 < baseStart_3922213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922226 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_3922226 : Nat := 118140960795 + 3922226 * 2 ^ 59
def prefixEnd_3922226 : Nat := 4983230072969 + 3 ^ 40 * 3922226 * 2
def baseEnd_3922226 : Nat := 671329057853892168812339

theorem tailTrace_3922226 : CollatzResearch.WordTrace tailWord_3922226 prefixEnd_3922226 671329057853892168812339 := by
  unfold tailWord_3922226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35763833672113134928850633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95370223125635026476935021 35763833672113134928850633)
  ·
    refine ⟨26822875254084851196637975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35763833672113134928850633 26822875254084851196637975)
    ·
      refine ⟨40234312881127276794956963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26822875254084851196637975 40234312881127276794956963)
      ·
        refine ⟨60351469321690915192435445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40234312881127276794956963 60351469321690915192435445)
        ·
          refine ⟨5657950248908523299290823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60351469321690915192435445 5657950248908523299290823)
          ·
            refine ⟨8486925373362784948936235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657950248908523299290823 8486925373362784948936235)
            ·
              refine ⟨12730388060044177423404353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8486925373362784948936235 12730388060044177423404353)
              ·
                refine ⟨9547791045033133067553265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12730388060044177423404353 9547791045033133067553265)
                ·
                  refine ⟨7160843283774849800664949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9547791045033133067553265 7160843283774849800664949)
                  ·
                    refine ⟨671329057853892168812339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7160843283774849800664949 671329057853892168812339)
                    ·
                      rfl

theorem cell23_3922226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_3922226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922226 prefixEnd_3922226 := by exact prefixLift 3922226
  have htrace : WordTrace (prefixWord ++ tailWord_3922226) baseStart_3922226 baseEnd_3922226 := by
    simpa [prefixWord, tailWord_3922226, baseEnd_3922226] using wordTrace_append hprefix tailTrace_3922226
  have hstable : (prefixWord ++ tailWord_3922226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922226).length < 2 ^ (prefixWord ++ tailWord_3922226).sum := by decide
  have hdescent : baseEnd_3922226 < baseStart_3922226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922249 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 3]
def baseStart_3922249 : Nat := 118140960795 + 3922249 * 2 ^ 59
def prefixEnd_3922249 : Nat := 4983230072969 + 3 ^ 40 * 3922249 * 2
def baseEnd_3922249 : Nat := 2013998983616729916449411

theorem tailTrace_3922249 : CollatzResearch.WordTrace tailWord_3922249 prefixEnd_3922249 2013998983616729916449411 := by
  unfold tailWord_3922249
  simp only [CollatzResearch.WordTrace]
  refine ⟨143056173567369214643489801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95370782378246143095659867 143056173567369214643489801)
  ·
    refine ⟨107292130175526910982617351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143056173567369214643489801 107292130175526910982617351)
    ·
      refine ⟨160938195263290366473926027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107292130175526910982617351 160938195263290366473926027)
      ·
        refine ⟨241407292894935549710889041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160938195263290366473926027 241407292894935549710889041)
        ·
          refine ⟨181055469671201662283166781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241407292894935549710889041 181055469671201662283166781)
          ·
            refine ⟨67895801126700623356187543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181055469671201662283166781 67895801126700623356187543)
            ·
              refine ⟨101843701690050935034281315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67895801126700623356187543 101843701690050935034281315)
              ·
                refine ⟨152765552535076402551421973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101843701690050935034281315 152765552535076402551421973)
                ·
                  refine ⟨7160885275081706369597905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152765552535076402551421973 7160885275081706369597905)
                  ·
                    refine ⟨5370663956311279777198429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7160885275081706369597905 5370663956311279777198429)
                    ·
                      refine ⟨2013998983616729916449411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5370663956311279777198429 2013998983616729916449411)
                      ·
                        rfl

theorem cell23_3922249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_3922249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922249 prefixEnd_3922249 := by exact prefixLift 3922249
  have htrace : WordTrace (prefixWord ++ tailWord_3922249) baseStart_3922249 baseEnd_3922249 := by
    simpa [prefixWord, tailWord_3922249, baseEnd_3922249] using wordTrace_append hprefix tailTrace_3922249
  have hstable : (prefixWord ++ tailWord_3922249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922249).length < 2 ^ (prefixWord ++ tailWord_3922249).sum := by decide
  have hdescent : baseEnd_3922249 < baseStart_3922249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922290 : List Nat := [3, 2, 1, 2, 1, 3, 4, 2, 1, 4]
def baseStart_3922290 : Nat := 118140960795 + 3922290 * 2 ^ 59
def prefixEnd_3922290 : Nat := 4983230072969 + 3 ^ 40 * 3922290 * 2
def baseEnd_3922290 : Nat := 671340012107854752012241

theorem tailTrace_3922290 : CollatzResearch.WordTrace tailWord_3922290 prefixEnd_3922290 671340012107854752012241 := by
  unfold tailWord_3922290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35764417240055169661433081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95371779306813785763821549 35764417240055169661433081)
  ·
    refine ⟨26823312930041377246074811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35764417240055169661433081 26823312930041377246074811)
    ·
      refine ⟨40234969395062065869112217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26823312930041377246074811 40234969395062065869112217)
      ·
        refine ⟨30176227046296549401834163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40234969395062065869112217 30176227046296549401834163)
        ·
          refine ⟨45264340569444824102751245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30176227046296549401834163 45264340569444824102751245)
          ·
            refine ⟨16974127713541809038531717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45264340569444824102751245 16974127713541809038531717)
            ·
              refine ⟨3182648946289089194724697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16974127713541809038531717 3182648946289089194724697)
              ·
                refine ⟨2386986709716816896043523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182648946289089194724697 2386986709716816896043523)
                ·
                  refine ⟨3580480064575225344065285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386986709716816896043523 3580480064575225344065285)
                  ·
                    refine ⟨671340012107854752012241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580480064575225344065285 671340012107854752012241)
                    ·
                      rfl

theorem cell23_3922290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_3922290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922290 prefixEnd_3922290 := by exact prefixLift 3922290
  have htrace : WordTrace (prefixWord ++ tailWord_3922290) baseStart_3922290 baseEnd_3922290 := by
    simpa [prefixWord, tailWord_3922290, baseEnd_3922290] using wordTrace_append hprefix tailTrace_3922290
  have hstable : (prefixWord ++ tailWord_3922290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922290).length < 2 ^ (prefixWord ++ tailWord_3922290).sum := by decide
  have hdescent : baseEnd_3922290 < baseStart_3922290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922299 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 3, 5]
def baseStart_3922299 : Nat := 118140960795 + 3922299 * 2 ^ 59
def prefixEnd_3922299 : Nat := 4983230072969 + 3 ^ 40 * 3922299 * 2
def baseEnd_3922299 : Nat := 671341552549818240274727

theorem tailTrace_3922299 : CollatzResearch.WordTrace tailWord_3922299 prefixEnd_3922299 671341552549818240274727 := by
  unfold tailWord_3922299
  simp only [CollatzResearch.WordTrace]
  refine ⟨143057997217188073182809951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95371998144792048788539967 143057997217188073182809951)
  ·
    refine ⟨214586995825782109774214927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143057997217188073182809951 214586995825782109774214927)
    ·
      refine ⟨321880493738673164661322391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214586995825782109774214927 321880493738673164661322391)
      ·
        refine ⟨482820740608009746991983587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321880493738673164661322391 482820740608009746991983587)
        ·
          refine ⟨724231110912014620487975381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482820740608009746991983587 724231110912014620487975381)
          ·
            refine ⟨16974166662000342667686923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 724231110912014620487975381 16974166662000342667686923)
            ·
              refine ⟨25461249993000514001530385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16974166662000342667686923 25461249993000514001530385)
              ·
                refine ⟨19095937494750385501147789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25461249993000514001530385 19095937494750385501147789)
                ·
                  refine ⟨7160976560531394562930421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19095937494750385501147789 7160976560531394562930421)
                  ·
                    refine ⟨671341552549818240274727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7160976560531394562930421 671341552549818240274727)
                    ·
                      rfl

theorem cell23_3922299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 5].length) (baseStart_3922299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922299 prefixEnd_3922299 := by exact prefixLift 3922299
  have htrace : WordTrace (prefixWord ++ tailWord_3922299) baseStart_3922299 baseEnd_3922299 := by
    simpa [prefixWord, tailWord_3922299, baseEnd_3922299] using wordTrace_append hprefix tailTrace_3922299
  have hstable : (prefixWord ++ tailWord_3922299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922299).length < 2 ^ (prefixWord ++ tailWord_3922299).sum := by decide
  have hdescent : baseEnd_3922299 < baseStart_3922299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922313 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 3]
def baseStart_3922313 : Nat := 118140960795 + 3922313 * 2 ^ 59
def prefixEnd_3922313 : Nat := 4983230072969 + 3 ^ 40 * 3922313 * 2
def baseEnd_3922313 : Nat := 2014031846378617666049117

theorem tailTrace_3922313 : CollatzResearch.WordTrace tailWord_3922313 prefixEnd_3922313 2014031846378617666049117 := by
  unfold tailWord_3922313
  simp only [CollatzResearch.WordTrace]
  refine ⟨143058507839137353573819593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95372338559424902382546395 143058507839137353573819593)
  ·
    refine ⟨107293880879353015180364695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143058507839137353573819593 107293880879353015180364695)
    ·
      refine ⟨160940821319029522770547043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107293880879353015180364695 160940821319029522770547043)
      ·
        refine ⟨241411231978544284155820565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160940821319029522770547043 241411231978544284155820565)
        ·
          refine ⟨11316151498994263319804089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241411231978544284155820565 11316151498994263319804089)
          ·
            refine ⟨8487113624245697489853067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11316151498994263319804089 8487113624245697489853067)
            ·
              refine ⟨12730670436368546234779601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487113624245697489853067 12730670436368546234779601)
              ·
                refine ⟨9548002827276409676084701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12730670436368546234779601 9548002827276409676084701)
                ·
                  refine ⟨3580501060228653628531763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9548002827276409676084701 3580501060228653628531763)
                  ·
                    refine ⟨5370751590342980442797645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3580501060228653628531763 5370751590342980442797645)
                    ·
                      refine ⟨2014031846378617666049117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5370751590342980442797645 2014031846378617666049117)
                      ·
                        rfl

theorem cell23_3922313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 3, 1, 3].length) (baseStart_3922313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922313 prefixEnd_3922313 := by exact prefixLift 3922313
  have htrace : WordTrace (prefixWord ++ tailWord_3922313) baseStart_3922313 baseEnd_3922313 := by
    simpa [prefixWord, tailWord_3922313, baseEnd_3922313] using wordTrace_append hprefix tailTrace_3922313
  have hstable : (prefixWord ++ tailWord_3922313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922313).length < 2 ^ (prefixWord ++ tailWord_3922313).sum := by decide
  have hdescent : baseEnd_3922313 < baseStart_3922313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922329 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 1, 6]
def baseStart_3922329 : Nat := 118140960795 + 3922329 * 2 ^ 59
def prefixEnd_3922329 : Nat := 4983230072969 + 3 ^ 40 * 3922329 * 2
def baseEnd_3922329 : Nat := 671346687356363201149681

theorem tailTrace_3922329 : CollatzResearch.WordTrace tailWord_3922329 prefixEnd_3922329 671346687356363201149681 := by
  unfold tailWord_3922329
  simp only [CollatzResearch.WordTrace]
  refine ⟨143059091407079388306402041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95372727604719592204268027 143059091407079388306402041)
  ·
    refine ⟨107294318555309541229801531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143059091407079388306402041 107294318555309541229801531)
    ·
      refine ⟨160941477832964311844702297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107294318555309541229801531 160941477832964311844702297)
      ·
        refine ⟨120706108374723233883526723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160941477832964311844702297 120706108374723233883526723)
        ·
          refine ⟨181059162562084850825290085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120706108374723233883526723 181059162562084850825290085)
          ·
            refine ⟨33948592980390909529741891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181059162562084850825290085 33948592980390909529741891)
            ·
              refine ⟨50922889470586364294612837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33948592980390909529741891 50922889470586364294612837)
              ·
                refine ⟨9548041775734943305239907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50922889470586364294612837 9548041775734943305239907)
                ·
                  refine ⟨14322062663602414957859861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548041775734943305239907 14322062663602414957859861)
                  ·
                    refine ⟨671346687356363201149681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14322062663602414957859861 671346687356363201149681)
                    ·
                      rfl

theorem cell23_3922329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_3922329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922329 prefixEnd_3922329 := by exact prefixLift 3922329
  have htrace : WordTrace (prefixWord ++ tailWord_3922329) baseStart_3922329 baseEnd_3922329 := by
    simpa [prefixWord, tailWord_3922329, baseEnd_3922329] using wordTrace_append hprefix tailTrace_3922329
  have hstable : (prefixWord ++ tailWord_3922329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922329).length < 2 ^ (prefixWord ++ tailWord_3922329).sum := by decide
  have hdescent : baseEnd_3922329 < baseStart_3922329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922330 : List Nat := [3, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3]
def baseStart_3922330 : Nat := 118140960795 + 3922330 * 2 ^ 59
def prefixEnd_3922330 : Nat := 4983230072969 + 3 ^ 40 * 3922330 * 2
def baseEnd_3922330 : Nat := 2014040575549744099536539

theorem tailTrace_3922330 : CollatzResearch.WordTrace tailWord_3922330 prefixEnd_3922330 2014040575549744099536539 := by
  unfold tailWord_3922330
  simp only [CollatzResearch.WordTrace]
  refine ⟨35764781970018941369297111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95372751920050510318125629 35764781970018941369297111)
  ·
    refine ⟨53647172955028412053945667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35764781970018941369297111 53647172955028412053945667)
    ·
      refine ⟨80470759432542618080918501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53647172955028412053945667 80470759432542618080918501)
      ·
        refine ⟨15088267393601740890172219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80470759432542618080918501 15088267393601740890172219)
        ·
          refine ⟨22632401090402611335258329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15088267393601740890172219 22632401090402611335258329)
          ·
            refine ⟨16974300817801958501443747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22632401090402611335258329 16974300817801958501443747)
            ·
              refine ⟨25461451226702937752165621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16974300817801958501443747 25461451226702937752165621)
              ·
                refine ⟨2387011052503400414265527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25461451226702937752165621 2387011052503400414265527)
                ·
                  refine ⟨3580516578755100621398291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387011052503400414265527 3580516578755100621398291)
                  ·
                    refine ⟨5370774868132650932097437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3580516578755100621398291 5370774868132650932097437)
                    ·
                      refine ⟨2014040575549744099536539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5370774868132650932097437 2014040575549744099536539)
                      ·
                        rfl

theorem cell23_3922330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_3922330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922330 prefixEnd_3922330 := by exact prefixLift 3922330
  have htrace : WordTrace (prefixWord ++ tailWord_3922330) baseStart_3922330 baseEnd_3922330 := by
    simpa [prefixWord, tailWord_3922330, baseEnd_3922330] using wordTrace_append hprefix tailTrace_3922330
  have hstable : (prefixWord ++ tailWord_3922330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922330).length < 2 ^ (prefixWord ++ tailWord_3922330).sum := by decide
  have hdescent : baseEnd_3922330 < baseStart_3922330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922333 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3922333 : Nat := 118140960795 + 3922333 * 2 ^ 59
def prefixEnd_3922333 : Nat := 4983230072969 + 3 ^ 40 * 3922333 * 2
def baseEnd_3922333 : Nat := 671347371997235862599675

theorem tailTrace_3922333 : CollatzResearch.WordTrace tailWord_3922333 prefixEnd_3922333 671347371997235862599675 := by
  unfold tailWord_3922333
  simp only [CollatzResearch.WordTrace]
  refine ⟨143059237299064896989547653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95372824866043264659698435 143059237299064896989547653)
  ·
    refine ⟨26823606993574668185540185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143059237299064896989547653 26823606993574668185540185)
    ·
      refine ⟨20117705245181001139155139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26823606993574668185540185 20117705245181001139155139)
      ·
        refine ⟨30176557867771501708732709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20117705245181001139155139 30176557867771501708732709)
        ·
          refine ⟨5658104600207156570387383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30176557867771501708732709 5658104600207156570387383)
          ·
            refine ⟨8487156900310734855581075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658104600207156570387383 8487156900310734855581075)
            ·
              refine ⟨12730735350466102283371613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487156900310734855581075 12730735350466102283371613)
              ·
                refine ⟨4774025756424788356264355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12730735350466102283371613 4774025756424788356264355)
                ·
                  refine ⟨7161038634637182534396533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774025756424788356264355 7161038634637182534396533)
                  ·
                    refine ⟨671347371997235862599675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7161038634637182534396533 671347371997235862599675)
                    ·
                      rfl

theorem cell23_3922333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3922333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922333 prefixEnd_3922333 := by exact prefixLift 3922333
  have htrace : WordTrace (prefixWord ++ tailWord_3922333) baseStart_3922333 baseEnd_3922333 := by
    simpa [prefixWord, tailWord_3922333, baseEnd_3922333] using wordTrace_append hprefix tailTrace_3922333
  have hstable : (prefixWord ++ tailWord_3922333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922333).length < 2 ^ (prefixWord ++ tailWord_3922333).sum := by decide
  have hdescent : baseEnd_3922333 < baseStart_3922333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922376 : List Nat := [2, 1, 3, 1, 3, 2, 4, 7]
def baseStart_3922376 : Nat := 118140960795 + 3922376 * 2 ^ 59
def prefixEnd_3922376 : Nat := 4983230072969 + 3 ^ 40 * 3922376 * 2
def baseEnd_3922376 : Nat := 74594970209624108131901

theorem tailTrace_3922376 : CollatzResearch.WordTrace tailWord_3922376 prefixEnd_3922376 74594970209624108131901 := by
  unfold tailWord_3922376
  simp only [CollatzResearch.WordTrace]
  refine ⟨71530402818954557666681491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95373870425272743555575321 71530402818954557666681491)
  ·
    refine ⟨107295604228431836500022237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71530402818954557666681491 107295604228431836500022237)
    ·
      refine ⟨40235851585661938687508339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107295604228431836500022237 40235851585661938687508339)
      ·
        refine ⟨60353777378492908031262509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40235851585661938687508339 60353777378492908031262509)
        ·
          refine ⟨22632666516934840511723441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60353777378492908031262509 22632666516934840511723441)
          ·
            refine ⟨16974499887701130383792581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22632666516934840511723441 16974499887701130383792581)
            ·
              refine ⟨3182718728943961946961109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16974499887701130383792581 3182718728943961946961109)
              ·
                refine ⟨74594970209624108131901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3182718728943961946961109 74594970209624108131901)
                ·
                  rfl

theorem cell23_3922376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 7].length) (baseStart_3922376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922376 prefixEnd_3922376 := by exact prefixLift 3922376
  have htrace : WordTrace (prefixWord ++ tailWord_3922376) baseStart_3922376 baseEnd_3922376 := by
    simpa [prefixWord, tailWord_3922376, baseEnd_3922376] using wordTrace_append hprefix tailTrace_3922376
  have hstable : (prefixWord ++ tailWord_3922376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922376).length < 2 ^ (prefixWord ++ tailWord_3922376).sum := by decide
  have hdescent : baseEnd_3922376 < baseStart_3922376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922390 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3922390 : Nat := 118140960795 + 3922390 * 2 ^ 59
def prefixEnd_3922390 : Nat := 4983230072969 + 3 ^ 40 * 3922390 * 2
def baseEnd_3922390 : Nat := 2014071384389013864786263

theorem tailTrace_3922390 : CollatzResearch.WordTrace tailWord_3922390 prefixEnd_3922390 2014071384389013864786263 := by
  unfold tailWord_3922390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941332266241149732773289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95374210839905597149581749 8941332266241149732773289)
  ·
    refine ⟨6705999199680862299579967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8941332266241149732773289 6705999199680862299579967)
    ·
      refine ⟨10058998799521293449369951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6705999199680862299579967 10058998799521293449369951)
      ·
        refine ⟨15088498199281940174054927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10058998799521293449369951 15088498199281940174054927)
        ·
          refine ⟨22632747298922910261082391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15088498199281940174054927 22632747298922910261082391)
          ·
            refine ⟨33949120948384365391623587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22632747298922910261082391 33949120948384365391623587)
            ·
              refine ⟨50923681422576548087435381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33949120948384365391623587 50923681422576548087435381)
              ·
                refine ⟨4774095133366551383197067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50923681422576548087435381 4774095133366551383197067)
                ·
                  refine ⟨7161142700049827074795601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774095133366551383197067 7161142700049827074795601)
                  ·
                    refine ⟨5370857025037370306096701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7161142700049827074795601 5370857025037370306096701)
                    ·
                      refine ⟨2014071384389013864786263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5370857025037370306096701 2014071384389013864786263)
                      ·
                        rfl

theorem cell23_3922390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3922390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922390 prefixEnd_3922390 := by exact prefixLift 3922390
  have htrace : WordTrace (prefixWord ++ tailWord_3922390) baseStart_3922390 baseEnd_3922390 := by
    simpa [prefixWord, tailWord_3922390, baseEnd_3922390] using wordTrace_append hprefix tailTrace_3922390
  have hstable : (prefixWord ++ tailWord_3922390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922390).length < 2 ^ (prefixWord ++ tailWord_3922390).sum := by decide
  have hdescent : baseEnd_3922390 < baseStart_3922390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922419 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 1, 8]
def baseStart_3922419 : Nat := 118140960795 + 3922419 * 2 ^ 59
def prefixEnd_3922419 : Nat := 4983230072969 + 3 ^ 40 * 3922419 * 2
def baseEnd_3922419 : Nat := 671362091775998083774543

theorem tailTrace_3922419 : CollatzResearch.WordTrace tailWord_3922419 prefixEnd_3922419 671362091775998083774543 := by
  unfold tailWord_3922419
  simp only [CollatzResearch.WordTrace]
  refine ⟨143062373976753333677178311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95374915984502222451452207 143062373976753333677178311)
  ·
    refine ⟨214593560965130000515767467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143062373976753333677178311 214593560965130000515767467)
    ·
      refine ⟨321890341447695000773651201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214593560965130000515767467 321890341447695000773651201)
      ·
        refine ⟨241417756085771250580238401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321890341447695000773651201 241417756085771250580238401)
        ·
          refine ⟨181063317064328437935178801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241417756085771250580238401 181063317064328437935178801)
          ·
            refine ⟨135797487798246328451384101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181063317064328437935178801 135797487798246328451384101)
            ·
              refine ⟨25462028962171186584634519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135797487798246328451384101 25462028962171186584634519)
              ·
                refine ⟨38193043443256779876951779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25462028962171186584634519 38193043443256779876951779)
                ·
                  refine ⟨57289565164885169815427669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38193043443256779876951779 57289565164885169815427669)
                  ·
                    refine ⟨671362091775998083774543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57289565164885169815427669 671362091775998083774543)
                    ·
                      rfl

theorem cell23_3922419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 8].length) (baseStart_3922419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922419 prefixEnd_3922419 := by exact prefixLift 3922419
  have htrace : WordTrace (prefixWord ++ tailWord_3922419) baseStart_3922419 baseEnd_3922419 := by
    simpa [prefixWord, tailWord_3922419, baseEnd_3922419] using wordTrace_append hprefix tailTrace_3922419
  have hstable : (prefixWord ++ tailWord_3922419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922419).length < 2 ^ (prefixWord ++ tailWord_3922419).sum := by decide
  have hdescent : baseEnd_3922419 < baseStart_3922419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922443 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 3, 4, 2]
def baseStart_3922443 : Nat := 118140960795 + 3922443 * 2 ^ 59
def prefixEnd_3922443 : Nat := 4983230072969 + 3 ^ 40 * 3922443 * 2
def baseEnd_3922443 : Nat := 2014098598863702157423519

theorem tailTrace_3922443 : CollatzResearch.WordTrace tailWord_3922443 prefixEnd_3922443 2014098598863702157423519 := by
  unfold tailWord_3922443
  simp only [CollatzResearch.WordTrace]
  refine ⟨143063249328666385776051983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95375499552444257184034655 143063249328666385776051983)
  ·
    refine ⟨214594873992999578664077975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143063249328666385776051983 214594873992999578664077975)
    ·
      refine ⟨321892310989499367996116963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214594873992999578664077975 321892310989499367996116963)
      ·
        refine ⟨482838466484249051994175445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321892310989499367996116963 482838466484249051994175445)
        ·
          refine ⟨11316526558224587156113487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 482838466484249051994175445 11316526558224587156113487)
          ·
            refine ⟨16974789837336880734170231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11316526558224587156113487 16974789837336880734170231)
            ·
              refine ⟨25462184756005321101255347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16974789837336880734170231 25462184756005321101255347)
              ·
                refine ⟨38193277134007981651883021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25462184756005321101255347 38193277134007981651883021)
                ·
                  refine ⟨14322478925252993119456133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38193277134007981651883021 14322478925252993119456133)
                  ·
                    refine ⟨2685464798484936209898025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14322478925252993119456133 2685464798484936209898025)
                    ·
                      refine ⟨2014098598863702157423519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685464798484936209898025 2014098598863702157423519)
                      ·
                        rfl

theorem cell23_3922443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4, 2].length) (baseStart_3922443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922443 prefixEnd_3922443 := by exact prefixLift 3922443
  have htrace : WordTrace (prefixWord ++ tailWord_3922443) baseStart_3922443 baseEnd_3922443 := by
    simpa [prefixWord, tailWord_3922443, baseEnd_3922443] using wordTrace_append hprefix tailTrace_3922443
  have hstable : (prefixWord ++ tailWord_3922443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922443).length < 2 ^ (prefixWord ++ tailWord_3922443).sum := by decide
  have hdescent : baseEnd_3922443 < baseStart_3922443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922449 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 11]
def baseStart_3922449 : Nat := 118140960795 + 3922449 * 2 ^ 59
def prefixEnd_3922449 : Nat := 4983230072969 + 3 ^ 40 * 3922449 * 2
def baseEnd_3922449 : Nat := 223789075527514348216499

theorem tailTrace_3922449 : CollatzResearch.WordTrace tailWord_3922449 prefixEnd_3922449 223789075527514348216499 := by
  unfold tailWord_3922449
  simp only [CollatzResearch.WordTrace]
  refine ⟨143063468166644648800770401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95375645444429765867180267 143063468166644648800770401)
  ·
    refine ⟨107297601124983486600577801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143063468166644648800770401 107297601124983486600577801)
    ·
      refine ⟨80473200843737614950433351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107297601124983486600577801 80473200843737614950433351)
      ·
        refine ⟨120709801265606422425650027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80473200843737614950433351 120709801265606422425650027)
        ·
          refine ⟨181064701898409633638475041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120709801265606422425650027 181064701898409633638475041)
          ·
            refine ⟨135798526423807225228856281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181064701898409633638475041 135798526423807225228856281)
            ·
              refine ⟨101848894817855418921642211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135798526423807225228856281 101848894817855418921642211)
              ·
                refine ⟨152773342226783128382463317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101848894817855418921642211 152773342226783128382463317)
                ·
                  refine ⟨223789075527514348216499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 152773342226783128382463317 223789075527514348216499)
                  ·
                    rfl

theorem cell23_3922449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 11].length) (baseStart_3922449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922449 prefixEnd_3922449 := by exact prefixLift 3922449
  have htrace : WordTrace (prefixWord ++ tailWord_3922449) baseStart_3922449 baseEnd_3922449 := by
    simpa [prefixWord, tailWord_3922449, baseEnd_3922449] using wordTrace_append hprefix tailTrace_3922449
  have hstable : (prefixWord ++ tailWord_3922449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922449).length < 2 ^ (prefixWord ++ tailWord_3922449).sum := by decide
  have hdescent : baseEnd_3922449 < baseStart_3922449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922466 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 7]
def baseStart_3922466 : Nat := 118140960795 + 3922466 * 2 ^ 59
def prefixEnd_3922466 : Nat := 4983230072969 + 3 ^ 40 * 3922466 * 2
def baseEnd_3922466 : Nat := 223790045435417285270657

theorem tailTrace_3922466 : CollatzResearch.WordTrace tailWord_3922466 prefixEnd_3922466 223790045435417285270657 := by
  unfold tailWord_3922466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35766022051895765176034813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95376058805055373802759501 35766022051895765176034813)
  ·
    refine ⟨13412258269460911941013055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35766022051895765176034813 13412258269460911941013055)
    ·
      refine ⟨20118387404191367911519583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13412258269460911941013055 20118387404191367911519583)
      ·
        refine ⟨30177581106287051867279375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20118387404191367911519583 30177581106287051867279375)
        ·
          refine ⟨45266371659430577800919063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30177581106287051867279375 45266371659430577800919063)
          ·
            refine ⟨67899557489145866701378595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45266371659430577800919063 67899557489145866701378595)
            ·
              refine ⟨101849336233718800052067893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67899557489145866701378595 101849336233718800052067893)
              ·
                refine ⟨9548375271911137504881365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101849336233718800052067893 9548375271911137504881365)
                ·
                  refine ⟨223790045435417285270657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9548375271911137504881365 223790045435417285270657)
                  ·
                    rfl

theorem cell23_3922466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_3922466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922466 prefixEnd_3922466 := by exact prefixLift 3922466
  have htrace : WordTrace (prefixWord ++ tailWord_3922466) baseStart_3922466 baseEnd_3922466 := by
    simpa [prefixWord, tailWord_3922466, baseEnd_3922466] using wordTrace_append hprefix tailTrace_3922466
  have hstable : (prefixWord ++ tailWord_3922466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922466).length < 2 ^ (prefixWord ++ tailWord_3922466).sum := by decide
  have hdescent : baseEnd_3922466 < baseStart_3922466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922543 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 3, 4]
def baseStart_3922543 : Nat := 118140960795 + 3922543 * 2 ^ 59
def prefixEnd_3922543 : Nat := 4983230072969 + 3 ^ 40 * 3922543 * 2
def baseEnd_3922543 : Nat := 671383315643050588724353

theorem tailTrace_3922543 : CollatzResearch.WordTrace tailWord_3922543 prefixEnd_3922543 671383315643050588724353 := by
  unfold tailWord_3922543
  simp only [CollatzResearch.WordTrace]
  refine ⟨143066896628304102854692283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95377931085536068569794855 143066896628304102854692283)
  ·
    refine ⟨214600344942456154282038425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143066896628304102854692283 214600344942456154282038425)
    ·
      refine ⟨160950258706842115711528819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214600344942456154282038425 160950258706842115711528819)
      ·
        refine ⟨241425388060263173567293229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160950258706842115711528819 241425388060263173567293229)
        ·
          refine ⟨90534520522598690087734961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241425388060263173567293229 90534520522598690087734961)
          ·
            refine ⟨67900890391949017565801221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90534520522598690087734961 67900890391949017565801221)
            ·
              refine ⟨12731416948490440793587729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67900890391949017565801221 12731416948490440793587729)
              ·
                refine ⟨9548562711367830595190797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12731416948490440793587729 9548562711367830595190797)
                ·
                  refine ⟨3580711016762936473196549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9548562711367830595190797 3580711016762936473196549)
                  ·
                    refine ⟨671383315643050588724353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580711016762936473196549 671383315643050588724353)
                    ·
                      rfl

theorem cell23_3922543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_3922543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922543 prefixEnd_3922543 := by exact prefixLift 3922543
  have htrace : WordTrace (prefixWord ++ tailWord_3922543) baseStart_3922543 baseEnd_3922543 := by
    simpa [prefixWord, tailWord_3922543, baseEnd_3922543] using wordTrace_append hprefix tailTrace_3922543
  have hstable : (prefixWord ++ tailWord_3922543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922543).length < 2 ^ (prefixWord ++ tailWord_3922543).sum := by decide
  have hdescent : baseEnd_3922543 < baseStart_3922543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922553 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 3]
def baseStart_3922553 : Nat := 118140960795 + 3922553 * 2 ^ 59
def prefixEnd_3922553 : Nat := 4983230072969 + 3 ^ 40 * 3922553 * 2
def baseEnd_3922553 : Nat := 2014155081735696727048013

theorem tailTrace_3922553 : CollatzResearch.WordTrace tailWord_3922553 prefixEnd_3922553 2014155081735696727048013 := by
  unfold tailWord_3922553
  simp only [CollatzResearch.WordTrace]
  refine ⟨143067261358267874562556313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95378174238845249708370875 143067261358267874562556313)
  ·
    refine ⟨107300446018700905921917235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143067261358267874562556313 107300446018700905921917235)
    ·
      refine ⟨160950669028051358882875853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107300446018700905921917235 160950669028051358882875853)
      ·
        refine ⟨60356500885519259581078445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160950669028051358882875853 60356500885519259581078445)
        ·
          refine ⟨22633687832069722342904417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60356500885519259581078445 22633687832069722342904417)
          ·
            refine ⟨16975265874052291757178313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22633687832069722342904417 16975265874052291757178313)
            ·
              refine ⟨12731449405539218817883735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16975265874052291757178313 12731449405539218817883735)
              ·
                refine ⟨19097174108308828226825603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12731449405539218817883735 19097174108308828226825603)
                ·
                  refine ⟨28645761162463242340238405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19097174108308828226825603 28645761162463242340238405)
                  ·
                    refine ⟨5371080217961857938794701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28645761162463242340238405 5371080217961857938794701)
                    ·
                      refine ⟨2014155081735696727048013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371080217961857938794701 2014155081735696727048013)
                      ·
                        rfl

theorem cell23_3922553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_3922553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922553 prefixEnd_3922553 := by exact prefixLift 3922553
  have htrace : WordTrace (prefixWord ++ tailWord_3922553) baseStart_3922553 baseEnd_3922553 := by
    simpa [prefixWord, tailWord_3922553, baseEnd_3922553] using wordTrace_append hprefix tailTrace_3922553
  have hstable : (prefixWord ++ tailWord_3922553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922553).length < 2 ^ (prefixWord ++ tailWord_3922553).sum := by decide
  have hdescent : baseEnd_3922553 < baseStart_3922553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922556 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 8]
def baseStart_3922556 : Nat := 118140960795 + 3922556 * 2 ^ 59
def prefixEnd_3922556 : Nat := 4983230072969 + 3 ^ 40 * 3922556 * 2
def baseEnd_3922556 : Nat := 223795180241962246145611

theorem tailTrace_3922556 : CollatzResearch.WordTrace tailWord_3922556 prefixEnd_3922556 223795180241962246145611 := by
  unfold tailWord_3922556
  simp only [CollatzResearch.WordTrace]
  refine ⟨71533685388628503037457761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95378247184838004049943681 71533685388628503037457761)
  ·
    refine ⟨53650264041471377278093321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71533685388628503037457761 53650264041471377278093321)
    ·
      refine ⟨40237698031103532958569991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53650264041471377278093321 40237698031103532958569991)
      ·
        refine ⟨60356547046655299437854987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40237698031103532958569991 60356547046655299437854987)
        ·
          refine ⟨90534820569982949156782481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60356547046655299437854987 90534820569982949156782481)
          ·
            refine ⟨67901115427487211867586861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90534820569982949156782481 67901115427487211867586861)
            ·
              refine ⟨25462918285307704450345073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67901115427487211867586861 25462918285307704450345073)
              ·
                refine ⟨19097188713980778337758805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25462918285307704450345073 19097188713980778337758805)
                ·
                  refine ⟨223795180241962246145611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19097188713980778337758805 223795180241962246145611)
                  ·
                    rfl

theorem cell23_3922556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_3922556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922556 prefixEnd_3922556 := by exact prefixLift 3922556
  have htrace : WordTrace (prefixWord ++ tailWord_3922556) baseStart_3922556 baseEnd_3922556 := by
    simpa [prefixWord, tailWord_3922556, baseEnd_3922556] using wordTrace_append hprefix tailTrace_3922556
  have hstable : (prefixWord ++ tailWord_3922556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922556).length < 2 ^ (prefixWord ++ tailWord_3922556).sum := by decide
  have hdescent : baseEnd_3922556 < baseStart_3922556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922590 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3922590 : Nat := 118140960795 + 3922590 * 2 ^ 59
def prefixEnd_3922590 : Nat := 4983230072969 + 3 ^ 40 * 3922590 * 2
def baseEnd_3922590 : Nat := 223797120057768120253927

theorem tailTrace_3922590 : CollatzResearch.WordTrace tailWord_3922590 prefixEnd_3922590 223797120057768120253927 := by
  unfold tailWord_3922590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883576357391728735206653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95379073906089219921102149 17883576357391728735206653)
  ·
    refine ⟨6706341134021898275702495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17883576357391728735206653 6706341134021898275702495)
    ·
      refine ⟨10059511701032847413553743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706341134021898275702495 10059511701032847413553743)
      ·
        refine ⟨15089267551549271120330615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10059511701032847413553743 15089267551549271120330615)
        ·
          refine ⟨22633901327323906680495923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15089267551549271120330615 22633901327323906680495923)
          ·
            refine ⟨33950851990985860020743885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22633901327323906680495923 33950851990985860020743885)
            ·
              refine ⟨12731569496619697507778957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33950851990985860020743885 12731569496619697507778957)
              ·
                refine ⟨4774338561232386565417109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12731569496619697507778957 4774338561232386565417109)
                ·
                  refine ⟨223797120057768120253927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4774338561232386565417109 223797120057768120253927)
                  ·
                    rfl

theorem cell23_3922590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3922590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922590 prefixEnd_3922590 := by exact prefixLift 3922590
  have htrace : WordTrace (prefixWord ++ tailWord_3922590) baseStart_3922590 baseEnd_3922590 := by
    simpa [prefixWord, tailWord_3922590, baseEnd_3922590] using wordTrace_append hprefix tailTrace_3922590
  have hstable : (prefixWord ++ tailWord_3922590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922590).length < 2 ^ (prefixWord ++ tailWord_3922590).sum := by decide
  have hdescent : baseEnd_3922590 < baseStart_3922590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922617 : List Nat := [1, 2, 1, 4, 1, 1, 1, 7, 1, 1, 3]
def baseStart_3922617 : Nat := 118140960795 + 3922617 * 2 ^ 59
def prefixEnd_3922617 : Nat := 4983230072969 + 3 ^ 40 * 3922617 * 2
def baseEnd_3922617 : Nat := 2014187944497584476647719

theorem tailTrace_3922617 : CollatzResearch.WordTrace tailWord_3922617 prefixEnd_3922617 2014187944497584476647719 := by
  unfold tailWord_3922617
  simp only [CollatzResearch.WordTrace]
  refine ⟨143069595630036013492886105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95379730420024008995257403 143069595630036013492886105)
  ·
    refine ⟨107302196722527010119664579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143069595630036013492886105 107302196722527010119664579)
    ·
      refine ⟨160953295083790515179496869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107302196722527010119664579 160953295083790515179496869)
      ·
        refine ⟨30178742828210721596155663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160953295083790515179496869 30178742828210721596155663)
        ·
          refine ⟨45268114242316082394233495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30178742828210721596155663 45268114242316082394233495)
          ·
            refine ⟨67902171363474123591350243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45268114242316082394233495 67902171363474123591350243)
            ·
              refine ⟨101853257045211185387025365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67902171363474123591350243 101853257045211185387025365)
              ·
                refine ⟨2387185711997137157508407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101853257045211185387025365 2387185711997137157508407)
                ·
                  refine ⟨3580778567995705736262611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387185711997137157508407 3580778567995705736262611)
                  ·
                    refine ⟨5371167851993558604393917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3580778567995705736262611 5371167851993558604393917)
                    ·
                      refine ⟨2014187944497584476647719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371167851993558604393917 2014187944497584476647719)
                      ·
                        rfl

theorem cell23_3922617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_3922617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922617 prefixEnd_3922617 := by exact prefixLift 3922617
  have htrace : WordTrace (prefixWord ++ tailWord_3922617) baseStart_3922617 baseEnd_3922617 := by
    simpa [prefixWord, tailWord_3922617, baseEnd_3922617] using wordTrace_append hprefix tailTrace_3922617
  have hstable : (prefixWord ++ tailWord_3922617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922617).length < 2 ^ (prefixWord ++ tailWord_3922617).sum := by decide
  have hdescent : baseEnd_3922617 < baseStart_3922617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922634 : List Nat := [3, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_3922634 : Nat := 118140960795 + 3922634 * 2 ^ 59
def prefixEnd_3922634 : Nat := 4983230072969 + 3 ^ 40 * 3922634 * 2
def baseEnd_3922634 : Nat := 2014196673668710910135141

theorem tailTrace_3922634 : CollatzResearch.WordTrace tailWord_3922634 prefixEnd_3922634 2014196673668710910135141 := by
  unfold tailWord_3922634
  simp only [CollatzResearch.WordTrace]
  refine ⟨35767553917743606349063739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95380143780649616930836637 35767553917743606349063739)
  ·
    refine ⟨53651330876615409523595609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35767553917743606349063739 53651330876615409523595609)
    ·
      refine ⟨40238498157461557142696707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53651330876615409523595609 40238498157461557142696707)
      ·
        refine ⟨60357747236192335714045061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40238498157461557142696707 60357747236192335714045061)
        ·
          refine ⟨11317077606786062946383449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60357747236192335714045061 11317077606786062946383449)
          ·
            refine ⟨8487808205089547209787587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11317077606786062946383449 8487808205089547209787587)
            ·
              refine ⟨12731712307634320814681381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487808205089547209787587 12731712307634320814681381)
              ·
                refine ⟨2387196057681435152752759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12731712307634320814681381 2387196057681435152752759)
                ·
                  refine ⟨3580794086522152729129139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387196057681435152752759 3580794086522152729129139)
                  ·
                    refine ⟨5371191129783229093693709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3580794086522152729129139 5371191129783229093693709)
                    ·
                      refine ⟨2014196673668710910135141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371191129783229093693709 2014196673668710910135141)
                      ·
                        rfl

theorem cell23_3922634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_3922634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922634 prefixEnd_3922634 := by exact prefixLift 3922634
  have htrace : WordTrace (prefixWord ++ tailWord_3922634) baseStart_3922634 baseEnd_3922634 := by
    simpa [prefixWord, tailWord_3922634, baseEnd_3922634] using wordTrace_append hprefix tailTrace_3922634
  have hstable : (prefixWord ++ tailWord_3922634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922634).length < 2 ^ (prefixWord ++ tailWord_3922634).sum := by decide
  have hdescent : baseEnd_3922634 < baseStart_3922634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922650 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 2, 4]
def baseStart_3922650 : Nat := 118140960795 + 3922650 * 2 ^ 59
def prefixEnd_3922650 : Nat := 4983230072969 + 3 ^ 40 * 3922650 * 2
def baseEnd_3922650 : Nat := 671401629786394282511689

theorem tailTrace_3922650 : CollatzResearch.WordTrace tailWord_3922650 prefixEnd_3922650 671401629786394282511689 := by
  unfold tailWord_3922650
  simp only [CollatzResearch.WordTrace]
  refine ⟨35767699809729115032209351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95380532825944306752558269 35767699809729115032209351)
  ·
    refine ⟨53651549714593672548314027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35767699809729115032209351 53651549714593672548314027)
    ·
      refine ⟨80477324571890508822471041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53651549714593672548314027 80477324571890508822471041)
      ·
        refine ⟨60357993428917881616853281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80477324571890508822471041 60357993428917881616853281)
        ·
          refine ⟨45268495071688411212639961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60357993428917881616853281 45268495071688411212639961)
          ·
            refine ⟨33951371303766308409479971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45268495071688411212639961 33951371303766308409479971)
            ·
              refine ⟨50927056955649462614219957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33951371303766308409479971 50927056955649462614219957)
              ·
                refine ⟨4774411589592137120083121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50927056955649462614219957 4774411589592137120083121)
                ·
                  refine ⟨3580808692194102840062341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774411589592137120083121 3580808692194102840062341)
                  ·
                    refine ⟨671401629786394282511689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580808692194102840062341 671401629786394282511689)
                    ·
                      rfl

theorem cell23_3922650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_3922650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922650 prefixEnd_3922650 := by exact prefixLift 3922650
  have htrace : WordTrace (prefixWord ++ tailWord_3922650) baseStart_3922650 baseEnd_3922650 := by
    simpa [prefixWord, tailWord_3922650, baseEnd_3922650] using wordTrace_append hprefix tailTrace_3922650
  have hstable : (prefixWord ++ tailWord_3922650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922650).length < 2 ^ (prefixWord ++ tailWord_3922650).sum := by decide
  have hdescent : baseEnd_3922650 < baseStart_3922650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922657 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_3922657 : Nat := 118140960795 + 3922657 * 2 ^ 59
def prefixEnd_3922657 : Nat := 4983230072969 + 3 ^ 40 * 3922657 * 2
def baseEnd_3922657 : Nat := 2014208483723764320147535

theorem tailTrace_3922657 : CollatzResearch.WordTrace tailWord_3922657 prefixEnd_3922657 2014208483723764320147535 := by
  unfold tailWord_3922657
  simp only [CollatzResearch.WordTrace]
  refine ⟨143071054549891100324342225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95380703033260733549561483 143071054549891100324342225)
  ·
    refine ⟨107303290912418325243256669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143071054549891100324342225 107303290912418325243256669)
    ·
      refine ⟨40238734092156871966221251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107303290912418325243256669 40238734092156871966221251)
      ·
        refine ⟨60358101138235307949331877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40238734092156871966221251 60358101138235307949331877)
        ·
          refine ⟨11317143963419120240499727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60358101138235307949331877 11317143963419120240499727)
          ·
            refine ⟨16975715945128680360749591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11317143963419120240499727 16975715945128680360749591)
            ·
              refine ⟨25463573917693020541124387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16975715945128680360749591 25463573917693020541124387)
              ·
                refine ⟨38195360876539530811686581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25463573917693020541124387 38195360876539530811686581)
                ·
                  refine ⟨3580815082175581013595617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38195360876539530811686581 3580815082175581013595617)
                  ·
                    refine ⟨2685611311631685760196713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3580815082175581013595617 2685611311631685760196713)
                    ·
                      refine ⟨2014208483723764320147535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685611311631685760196713 2014208483723764320147535)
                      ·
                        rfl

theorem cell23_3922657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_3922657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922657 prefixEnd_3922657 := by exact prefixLift 3922657
  have htrace : WordTrace (prefixWord ++ tailWord_3922657) baseStart_3922657 baseEnd_3922657 := by
    simpa [prefixWord, tailWord_3922657, baseEnd_3922657] using wordTrace_append hprefix tailTrace_3922657
  have hstable : (prefixWord ++ tailWord_3922657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922657).length < 2 ^ (prefixWord ++ tailWord_3922657).sum := by decide
  have hdescent : baseEnd_3922657 < baseStart_3922657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922660 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_3922660 : Nat := 118140960795 + 3922660 * 2 ^ 59
def prefixEnd_3922660 : Nat := 4983230072969 + 3 ^ 40 * 3922660 * 2
def baseEnd_3922660 : Nat := 2014210024165727808410021

theorem tailTrace_3922660 : CollatzResearch.WordTrace tailWord_3922660 prefixEnd_3922660 2014210024165727808410021 := by
  unfold tailWord_3922660
  simp only [CollatzResearch.WordTrace]
  refine ⟨71535581984440115918350717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95380775979253487891134289 71535581984440115918350717)
  ·
    refine ⟨26825843244165043469381519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71535581984440115918350717 26825843244165043469381519)
    ·
      refine ⟨40238764866247565204072279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26825843244165043469381519 40238764866247565204072279)
      ·
        refine ⟨60358147299371347806108419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40238764866247565204072279 60358147299371347806108419)
        ·
          refine ⟨90537220949057021709162629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60358147299371347806108419 90537220949057021709162629)
          ·
            refine ⟨16975728927948191570467993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90537220949057021709162629 16975728927948191570467993)
            ·
              refine ⟨12731796695961143677850995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16975728927948191570467993 12731796695961143677850995)
              ·
                refine ⟨19097695043941715516776493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12731796695961143677850995 19097695043941715516776493)
                ·
                  refine ⟨7161635641478143318791185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19097695043941715516776493 7161635641478143318791185)
                  ·
                    refine ⟨5371226731108607489093389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7161635641478143318791185 5371226731108607489093389)
                    ·
                      refine ⟨2014210024165727808410021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371226731108607489093389 2014210024165727808410021)
                      ·
                        rfl

theorem cell23_3922660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_3922660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922660 prefixEnd_3922660 := by exact prefixLift 3922660
  have htrace : WordTrace (prefixWord ++ tailWord_3922660) baseStart_3922660 baseEnd_3922660 := by
    simpa [prefixWord, tailWord_3922660, baseEnd_3922660] using wordTrace_append hprefix tailTrace_3922660
  have hstable : (prefixWord ++ tailWord_3922660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922660).length < 2 ^ (prefixWord ++ tailWord_3922660).sum := by decide
  have hdescent : baseEnd_3922660 < baseStart_3922660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922670 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3922670 : Nat := 118140960795 + 3922670 * 2 ^ 59
def prefixEnd_3922670 : Nat := 4983230072969 + 3 ^ 40 * 3922670 * 2
def baseEnd_3922670 : Nat := 2014215158972272769284975

theorem tailTrace_3922670 : CollatzResearch.WordTrace tailWord_3922670 prefixEnd_3922670 2014215158972272769284975 := by
  unfold tailWord_3922670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17883941087355500443070683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95381019132562669029710309 17883941087355500443070683)
  ·
    refine ⟨26825911631033250664606025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17883941087355500443070683 26825911631033250664606025)
    ·
      refine ⟨20119433723274937998454519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26825911631033250664606025 20119433723274937998454519)
      ·
        refine ⟨30179150584912406997681779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20119433723274937998454519 30179150584912406997681779)
        ·
          refine ⟨45268725877368610496522669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30179150584912406997681779 45268725877368610496522669)
          ·
            refine ⟨16975772204013228936196001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45268725877368610496522669 16975772204013228936196001)
            ·
              refine ⟨12731829153009921702147001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16975772204013228936196001 12731829153009921702147001)
              ·
                refine ⟨9548871864757441276610251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12731829153009921702147001 9548871864757441276610251)
                ·
                  refine ⟨14323307797136161914915377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9548871864757441276610251 14323307797136161914915377)
                  ·
                    refine ⟨10742480847852121436186533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14323307797136161914915377 10742480847852121436186533)
                    ·
                      refine ⟨2014215158972272769284975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10742480847852121436186533 2014215158972272769284975)
                      ·
                        rfl

theorem cell23_3922670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3922670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922670 prefixEnd_3922670 := by exact prefixLift 3922670
  have htrace : WordTrace (prefixWord ++ tailWord_3922670) baseStart_3922670 baseEnd_3922670 := by
    simpa [prefixWord, tailWord_3922670, baseEnd_3922670] using wordTrace_append hprefix tailTrace_3922670
  have hstable : (prefixWord ++ tailWord_3922670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922670).length < 2 ^ (prefixWord ++ tailWord_3922670).sum := by decide
  have hdescent : baseEnd_3922670 < baseStart_3922670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922674 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_3922674 : Nat := 118140960795 + 3922674 * 2 ^ 59
def prefixEnd_3922674 : Nat := 4983230072969 + 3 ^ 40 * 3922674 * 2
def baseEnd_3922674 : Nat := 2014217212894890753634957

theorem tailTrace_3922674 : CollatzResearch.WordTrace tailWord_3922674 prefixEnd_3922674 2014217212894890753634957 := by
  unfold tailWord_3922674
  simp only [CollatzResearch.WordTrace]
  refine ⟨35767918647707378056927769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95381116393886341485140717 35767918647707378056927769)
  ·
    refine ⟨26825938985780533542695827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35767918647707378056927769 26825938985780533542695827)
    ·
      refine ⟨40238908478670800314043741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26825938985780533542695827 40238908478670800314043741)
      ·
        refine ⟨15089590679501550117766403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40238908478670800314043741 15089590679501550117766403)
        ·
          refine ⟨22634386019252325176649605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15089590679501550117766403 22634386019252325176649605)
          ·
            refine ⟨4243947378609810970621801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22634386019252325176649605 4243947378609810970621801)
            ·
              refine ⟨3182960533957358227966351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4243947378609810970621801 3182960533957358227966351)
              ·
                refine ⟨4774440800936037341949527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3182960533957358227966351 4774440800936037341949527)
                ·
                  refine ⟨7161661201404056012924291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4774440800936037341949527 7161661201404056012924291)
                  ·
                    refine ⟨10742491802106084019386437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7161661201404056012924291 10742491802106084019386437)
                    ·
                      refine ⟨2014217212894890753634957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10742491802106084019386437 2014217212894890753634957)
                      ·
                        rfl

theorem cell23_3922674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_3922674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922674 prefixEnd_3922674 := by exact prefixLift 3922674
  have htrace : WordTrace (prefixWord ++ tailWord_3922674) baseStart_3922674 baseEnd_3922674 := by
    simpa [prefixWord, tailWord_3922674, baseEnd_3922674] using wordTrace_append hprefix tailTrace_3922674
  have hstable : (prefixWord ++ tailWord_3922674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922674).length < 2 ^ (prefixWord ++ tailWord_3922674).sum := by decide
  have hdescent : baseEnd_3922674 < baseStart_3922674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922758 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3922758 : Nat := 118140960795 + 3922758 * 2 ^ 59
def prefixEnd_3922758 : Nat := 4983230072969 + 3 ^ 40 * 3922758 * 2
def baseEnd_3922758 : Nat := 2014260345269868424984571

theorem tailTrace_3922758 : CollatzResearch.WordTrace tailWord_3922758 prefixEnd_3922758 2014260345269868424984571 := by
  unfold tailWord_3922758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471085572578912330430279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95383158881683463049179285 4471085572578912330430279)
  ·
    refine ⟨6706628358868368495645419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4471085572578912330430279 6706628358868368495645419)
    ·
      refine ⟨10059942538302552743468129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706628358868368495645419 10059942538302552743468129)
      ·
        refine ⟨7544956903726914557601097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10059942538302552743468129 7544956903726914557601097)
        ·
          refine ⟨5658717677795185918200823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7544956903726914557601097 5658717677795185918200823)
          ·
            refine ⟨8488076516692778877301235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658717677795185918200823 8488076516692778877301235)
            ·
              refine ⟨12732114775039168315951853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488076516692778877301235 12732114775039168315951853)
              ·
                refine ⟨4774543040639688118481945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12732114775039168315951853 4774543040639688118481945)
                ·
                  refine ⟨3580907280479766088861459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774543040639688118481945 3580907280479766088861459)
                  ·
                    refine ⟨5371360920719649133292189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3580907280479766088861459 5371360920719649133292189)
                    ·
                      refine ⟨2014260345269868424984571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371360920719649133292189 2014260345269868424984571)
                      ·
                        rfl

theorem cell23_3922758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3922758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922758 prefixEnd_3922758 := by exact prefixLift 3922758
  have htrace : WordTrace (prefixWord ++ tailWord_3922758) baseStart_3922758 baseEnd_3922758 := by
    simpa [prefixWord, tailWord_3922758, baseEnd_3922758] using wordTrace_append hprefix tailTrace_3922758
  have hstable : (prefixWord ++ tailWord_3922758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922758).length < 2 ^ (prefixWord ++ tailWord_3922758).sum := by decide
  have hdescent : baseEnd_3922758 < baseStart_3922758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922798 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3922798 : Nat := 118140960795 + 3922798 * 2 ^ 59
def prefixEnd_3922798 : Nat := 4983230072969 + 3 ^ 40 * 3922798 * 2
def baseEnd_3922798 : Nat := 2014280884496048268484387

theorem tailTrace_3922798 : CollatzResearch.WordTrace tailWord_3922798 prefixEnd_3922798 2014280884496048268484387 := by
  unfold tailWord_3922798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884524655297535175653131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95384131494920187603483365 17884524655297535175653131)
  ·
    refine ⟨26826786982946302763479697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17884524655297535175653131 26826786982946302763479697)
    ·
      refine ⟨20120090237209727072609773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26826786982946302763479697 20120090237209727072609773)
      ·
        refine ⟨7545033838953647652228665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20120090237209727072609773 7545033838953647652228665)
        ·
          refine ⟨5658775379215235739171499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7545033838953647652228665 5658775379215235739171499)
          ·
            refine ⟨8488163068822853608757249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658775379215235739171499 8488163068822853608757249)
            ·
              refine ⟨6366122301617140206567937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8488163068822853608757249 6366122301617140206567937)
              ·
                refine ⟨4774591726212855154925953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366122301617140206567937 4774591726212855154925953)
                ·
                  refine ⟨3580943794659641366194465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774591726212855154925953 3580943794659641366194465)
                  ·
                    refine ⟨2685707845994731024645849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3580943794659641366194465 2685707845994731024645849)
                    ·
                      refine ⟨2014280884496048268484387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685707845994731024645849 2014280884496048268484387)
                      ·
                        rfl

theorem cell23_3922798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3922798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922798 prefixEnd_3922798 := by exact prefixLift 3922798
  have htrace : WordTrace (prefixWord ++ tailWord_3922798) baseStart_3922798 baseEnd_3922798 := by
    simpa [prefixWord, tailWord_3922798, baseEnd_3922798] using wordTrace_append hprefix tailTrace_3922798
  have hstable : (prefixWord ++ tailWord_3922798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922798).length < 2 ^ (prefixWord ++ tailWord_3922798).sum := by decide
  have hdescent : baseEnd_3922798 < baseStart_3922798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922800 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 2, 5]
def baseStart_3922800 : Nat := 118140960795 + 3922800 * 2 ^ 59
def prefixEnd_3922800 : Nat := 4983230072969 + 3 ^ 40 * 3922800 * 2
def baseEnd_3922800 : Nat := 671427303819119086886459

theorem tailTrace_3922800 : CollatzResearch.WordTrace tailWord_3922800 prefixEnd_3922800 671427303819119086886459 := by
  unfold tailWord_3922800
  simp only [CollatzResearch.WordTrace]
  refine ⟨71538135094186517873398927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95384180125582023831198569 71538135094186517873398927)
  ·
    refine ⟨107307202641279776810098391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71538135094186517873398927 107307202641279776810098391)
    ·
      refine ⟨160960803961919665215147587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107307202641279776810098391 160960803961919665215147587)
      ·
        refine ⟨241441205942879497822721381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160960803961919665215147587 241441205942879497822721381)
        ·
          refine ⟨45270226114289905841760259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241441205942879497822721381 45270226114289905841760259)
          ·
            refine ⟨67905339171434858762640389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45270226114289905841760259 67905339171434858762640389)
            ·
              refine ⟨12732251094644036017995073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67905339171434858762640389 12732251094644036017995073)
              ·
                refine ⟨9549188320983027013496305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12732251094644036017995073 9549188320983027013496305)
                ·
                  refine ⟨7161891240737270260122229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9549188320983027013496305 7161891240737270260122229)
                  ·
                    refine ⟨671427303819119086886459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7161891240737270260122229 671427303819119086886459)
                    ·
                      rfl

theorem cell23_3922800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_3922800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922800 prefixEnd_3922800 := by exact prefixLift 3922800
  have htrace : WordTrace (prefixWord ++ tailWord_3922800) baseStart_3922800 baseEnd_3922800 := by
    simpa [prefixWord, tailWord_3922800, baseEnd_3922800] using wordTrace_append hprefix tailTrace_3922800
  have hstable : (prefixWord ++ tailWord_3922800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922800).length < 2 ^ (prefixWord ++ tailWord_3922800).sum := by decide
  have hdescent : baseEnd_3922800 < baseStart_3922800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922820 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_3922820 : Nat := 118140960795 + 3922820 * 2 ^ 59
def prefixEnd_3922820 : Nat := 4983230072969 + 3 ^ 40 * 3922820 * 2
def baseEnd_3922820 : Nat := 2014292181070447182409285

theorem tailTrace_3922820 : CollatzResearch.WordTrace tailWord_3922820 prefixEnd_3922820 2014292181070447182409285 := by
  unfold tailWord_3922820
  simp only [CollatzResearch.WordTrace]
  refine ⟨71538499824150289581262957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95384666432200386108350609 71538499824150289581262957)
  ·
    refine ⟨26826937434056358592973609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71538499824150289581262957 26826937434056358592973609)
    ·
      refine ⟨20120203075542268944730207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26826937434056358592973609 20120203075542268944730207)
      ·
        refine ⟨30180304613313403417095311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20120203075542268944730207 30180304613313403417095311)
        ·
          refine ⟨45270456919970105125642967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30180304613313403417095311 45270456919970105125642967)
          ·
            refine ⟨67905685379955157688464451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45270456919970105125642967 67905685379955157688464451)
            ·
              refine ⟨101858528069932736532696677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67905685379955157688464451 101858528069932736532696677)
              ·
                refine ⟨19098474013112388099880627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101858528069932736532696677 19098474013112388099880627)
                ·
                  refine ⟨28647711019668582149820941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19098474013112388099880627 28647711019668582149820941)
                  ·
                    refine ⟨10742891632375718306182853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28647711019668582149820941 10742891632375718306182853)
                    ·
                      refine ⟨2014292181070447182409285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10742891632375718306182853 2014292181070447182409285)
                      ·
                        rfl

theorem cell23_3922820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_3922820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922820 prefixEnd_3922820 := by exact prefixLift 3922820
  have htrace : WordTrace (prefixWord ++ tailWord_3922820) baseStart_3922820 baseEnd_3922820 := by
    simpa [prefixWord, tailWord_3922820, baseEnd_3922820] using wordTrace_append hprefix tailTrace_3922820
  have hstable : (prefixWord ++ tailWord_3922820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922820).length < 2 ^ (prefixWord ++ tailWord_3922820).sum := by decide
  have hdescent : baseEnd_3922820 < baseStart_3922820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922837 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3922837 : Nat := 118140960795 + 3922837 * 2 ^ 59
def prefixEnd_3922837 : Nat := 4983230072969 + 3 ^ 40 * 3922837 * 2
def baseEnd_3922837 : Nat := 2014300910241573615896707

theorem tailTrace_3922837 : CollatzResearch.WordTrace tailWord_3922837 prefixEnd_3922837 2014300910241573615896707 := by
  unfold tailWord_3922837
  simp only [CollatzResearch.WordTrace]
  refine ⟨143077619689238991065894765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95385079792825994043929843 143077619689238991065894765)
  ·
    refine ⟨53654107383464621649710537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143077619689238991065894765 53654107383464621649710537)
    ·
      refine ⟨40240580537598466237282903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53654107383464621649710537 40240580537598466237282903)
      ·
        refine ⟨60360870806397699355924355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40240580537598466237282903 60360870806397699355924355)
        ·
          refine ⟨90541306209596549033886533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60360870806397699355924355 90541306209596549033886533)
          ·
            refine ⟨16976494914299352943853725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90541306209596549033886533 16976494914299352943853725)
            ·
              refine ⟨6366185592862257353945147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16976494914299352943853725 6366185592862257353945147)
              ·
                refine ⟨9549278389293386030917721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366185592862257353945147 9549278389293386030917721)
                ·
                  refine ⟨7161958791970039523188291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9549278389293386030917721 7161958791970039523188291)
                  ·
                    refine ⟨10742938187955059284782437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7161958791970039523188291 10742938187955059284782437)
                    ·
                      refine ⟨2014300910241573615896707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10742938187955059284782437 2014300910241573615896707)
                      ·
                        rfl

theorem cell23_3922837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3922837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922837 prefixEnd_3922837 := by exact prefixLift 3922837
  have htrace : WordTrace (prefixWord ++ tailWord_3922837) baseStart_3922837 baseEnd_3922837 := by
    simpa [prefixWord, tailWord_3922837, baseEnd_3922837] using wordTrace_append hprefix tailTrace_3922837
  have hstable : (prefixWord ++ tailWord_3922837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922837).length < 2 ^ (prefixWord ++ tailWord_3922837).sum := by decide
  have hdescent : baseEnd_3922837 < baseStart_3922837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922838 : List Nat := [5, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3922838 : Nat := 118140960795 + 3922838 * 2 ^ 59
def prefixEnd_3922838 : Nat := 4983230072969 + 3 ^ 40 * 3922838 * 2
def baseEnd_3922838 : Nat := 223811269302469790220467

theorem tailTrace_3922838 : CollatzResearch.WordTrace tailWord_3922838 prefixEnd_3922838 223811269302469790220467 := by
  unfold tailWord_3922838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8942353510139710514792573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95385104108156912157787445 8942353510139710514792573)
  ·
    refine ⟨3353382566302391443047215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8942353510139710514792573 3353382566302391443047215)
    ·
      refine ⟨5030073849453587164570823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353382566302391443047215 5030073849453587164570823)
      ·
        refine ⟨7545110774180380746856235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5030073849453587164570823 7545110774180380746856235)
        ·
          refine ⟨11317666161270571120284353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545110774180380746856235 11317666161270571120284353)
          ·
            refine ⟨8488249620952928340213265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11317666161270571120284353 8488249620952928340213265)
            ·
              refine ⟨6366187215714696255159949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8488249620952928340213265 6366187215714696255159949)
              ·
                refine ⟨2387320205893011095684981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6366187215714696255159949 2387320205893011095684981)
                ·
                  refine ⟨223811269302469790220467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2387320205893011095684981 223811269302469790220467)
                  ·
                    rfl

theorem cell23_3922838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3922838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922838 prefixEnd_3922838 := by exact prefixLift 3922838
  have htrace : WordTrace (prefixWord ++ tailWord_3922838) baseStart_3922838 baseEnd_3922838 := by
    simpa [prefixWord, tailWord_3922838, baseEnd_3922838] using wordTrace_append hprefix tailTrace_3922838
  have hstable : (prefixWord ++ tailWord_3922838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922838).length < 2 ^ (prefixWord ++ tailWord_3922838).sum := by decide
  have hdescent : baseEnd_3922838 < baseStart_3922838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922897 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 1, 5, 2]
def baseStart_3922897 : Nat := 118140960795 + 3922897 * 2 ^ 59
def prefixEnd_3922897 : Nat := 4983230072969 + 3 ^ 40 * 3922897 * 2
def baseEnd_3922897 : Nat := 2014331719080843381146431

theorem tailTrace_3922897 : CollatzResearch.WordTrace tailWord_3922897 prefixEnd_3922897 2014331719080843381146431 := by
  unfold tailWord_3922897
  simp only [CollatzResearch.WordTrace]
  refine ⟨143079808069021621313078945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95386538712681080875385963 143079808069021621313078945)
  ·
    refine ⟨107309856051766215984809209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143079808069021621313078945 107309856051766215984809209)
    ·
      refine ⟨80482392038824661988606907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107309856051766215984809209 80482392038824661988606907)
      ·
        refine ⟨120723588058236992982910361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80482392038824661988606907 120723588058236992982910361)
        ·
          refine ⟨90542691043677744737182771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120723588058236992982910361 90542691043677744737182771)
          ·
            refine ⟨135814036565516617105774157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90542691043677744737182771 135814036565516617105774157)
            ·
              refine ⟨50930263712068731414665309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135814036565516617105774157 50930263712068731414665309)
              ·
                refine ⟨19098848892025774280499491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50930263712068731414665309 19098848892025774280499491)
                ·
                  refine ⟨28648273338038661420749237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19098848892025774280499491 28648273338038661420749237)
                  ·
                    refine ⟨2685775625441124508195241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28648273338038661420749237 2685775625441124508195241)
                    ·
                      refine ⟨2014331719080843381146431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685775625441124508195241 2014331719080843381146431)
                      ·
                        rfl

theorem cell23_3922897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_3922897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922897 prefixEnd_3922897 := by exact prefixLift 3922897
  have htrace : WordTrace (prefixWord ++ tailWord_3922897) baseStart_3922897 baseEnd_3922897 := by
    simpa [prefixWord, tailWord_3922897, baseEnd_3922897] using wordTrace_append hprefix tailTrace_3922897
  have hstable : (prefixWord ++ tailWord_3922897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922897).length < 2 ^ (prefixWord ++ tailWord_3922897).sum := by decide
  have hdescent : baseEnd_3922897 < baseStart_3922897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922898 : List Nat := [3, 2, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_3922898 : Nat := 118140960795 + 3922898 * 2 ^ 59
def prefixEnd_3922898 : Nat := 4983230072969 + 3 ^ 40 * 3922898 * 2
def baseEnd_3922898 : Nat := 671444077520499292411309

theorem tailTrace_3922898 : CollatzResearch.WordTrace tailWord_3922898 prefixEnd_3922898 671444077520499292411309 := by
  unfold tailWord_3922898
  simp only [CollatzResearch.WordTrace]
  refine ⟨35769961135504499620966337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95386563028011998989243565 35769961135504499620966337)
  ·
    refine ⟨26827470851628374715724753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35769961135504499620966337 26827470851628374715724753)
    ·
      refine ⟨20120603138721281036793565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26827470851628374715724753 20120603138721281036793565)
      ·
        refine ⟨7545226177020480388797587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20120603138721281036793565 7545226177020480388797587)
        ·
          refine ⟨11317839265530720583196381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545226177020480388797587 11317839265530720583196381)
          ·
            refine ⟨4244189724574020218698643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11317839265530720583196381 4244189724574020218698643)
            ·
              refine ⟨6366284586861030328047965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244189724574020218698643 6366284586861030328047965)
              ·
                refine ⟨2387356720072886373017987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6366284586861030328047965 2387356720072886373017987)
                ·
                  refine ⟨3581035080109329559526981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387356720072886373017987 3581035080109329559526981)
                  ·
                    refine ⟨671444077520499292411309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3581035080109329559526981 671444077520499292411309)
                    ·
                      rfl

theorem cell23_3922898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_3922898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922898 prefixEnd_3922898 := by exact prefixLift 3922898
  have htrace : WordTrace (prefixWord ++ tailWord_3922898) baseStart_3922898 baseEnd_3922898 := by
    simpa [prefixWord, tailWord_3922898, baseEnd_3922898] using wordTrace_append hprefix tailTrace_3922898
  have hstable : (prefixWord ++ tailWord_3922898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922898).length < 2 ^ (prefixWord ++ tailWord_3922898).sum := by decide
  have hdescent : baseEnd_3922898 < baseStart_3922898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922972 : List Nat := [2, 2, 3, 1, 5, 1, 2, 2, 1, 1, 3]
def baseStart_3922972 : Nat := 118140960795 + 3922972 * 2 ^ 59
def prefixEnd_3922972 : Nat := 4983230072969 + 3 ^ 40 * 3922972 * 2
def baseEnd_3922972 : Nat := 2014370230129930587708587

theorem tailTrace_3922972 : CollatzResearch.WordTrace tailWord_3922972 prefixEnd_3922972 2014370230129930587708587 := by
  unfold tailWord_3922972
  simp only [CollatzResearch.WordTrace]
  refine ⟨71541271771874954561029585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95388362362499939414706113 71541271771874954561029585)
  ·
    refine ⟨53655953828906215920772189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71541271771874954561029585 53655953828906215920772189)
    ·
      refine ⟨20120982685839830970289571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53655953828906215920772189 20120982685839830970289571)
      ·
        refine ⟨30181474028759746455434357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20120982685839830970289571 30181474028759746455434357)
        ·
          refine ⟨2829513190196226230196971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30181474028759746455434357 2829513190196226230196971)
          ·
            refine ⟨4244269785294339345295457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829513190196226230196971 4244269785294339345295457)
            ·
              refine ⟨3183202338970754508971593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244269785294339345295457 3183202338970754508971593)
              ·
                refine ⟨2387401754228065881728695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183202338970754508971593 2387401754228065881728695)
                ·
                  refine ⟨3581102631342098822593043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387401754228065881728695 3581102631342098822593043)
                  ·
                    refine ⟨5371653947013148233889565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3581102631342098822593043 5371653947013148233889565)
                    ·
                      refine ⟨2014370230129930587708587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371653947013148233889565 2014370230129930587708587)
                      ·
                        rfl

theorem cell23_3922972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_3922972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922972 prefixEnd_3922972 := by exact prefixLift 3922972
  have htrace : WordTrace (prefixWord ++ tailWord_3922972) baseStart_3922972 baseEnd_3922972 := by
    simpa [prefixWord, tailWord_3922972, baseEnd_3922972] using wordTrace_append hprefix tailTrace_3922972
  have hstable : (prefixWord ++ tailWord_3922972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922972).length < 2 ^ (prefixWord ++ tailWord_3922972).sum := by decide
  have hdescent : baseEnd_3922972 < baseStart_3922972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3922994 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_3922994 : Nat := 118140960795 + 3922994 * 2 ^ 59
def prefixEnd_3922994 : Nat := 4983230072969 + 3 ^ 40 * 3922994 * 2
def baseEnd_3922994 : Nat := 2014381526704329501633485

theorem tailTrace_3922994 : CollatzResearch.WordTrace tailWord_3922994 prefixEnd_3922994 2014381526704329501633485 := by
  unfold tailWord_3922994
  simp only [CollatzResearch.WordTrace]
  refine ⟨35770836487417551719840009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95388897299780137919573357 35770836487417551719840009)
  ·
    refine ⟨26828127365563163789880007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35770836487417551719840009 26828127365563163789880007)
    ·
      refine ⟨40242191048344745684820011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26828127365563163789880007 40242191048344745684820011)
      ·
        refine ⟨60363286572517118527230017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40242191048344745684820011 60363286572517118527230017)
        ·
          refine ⟨45272464929387838895422513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60363286572517118527230017 45272464929387838895422513)
          ·
            refine ⟨33954348697040879171566885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45272464929387838895422513 33954348697040879171566885)
            ·
              refine ⟨6366440380695164844668791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33954348697040879171566885 6366440380695164844668791)
              ·
                refine ⟨9549660571042747267003187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366440380695164844668791 9549660571042747267003187)
                ·
                  refine ⟨14324490856564120900504781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9549660571042747267003187 14324490856564120900504781)
                  ·
                    refine ⟨5371684071211545337689293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14324490856564120900504781 5371684071211545337689293)
                    ·
                      refine ⟨2014381526704329501633485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371684071211545337689293 2014381526704329501633485)
                      ·
                        rfl

theorem cell23_3922994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_3922994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3922994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3922994 prefixEnd_3922994 := by exact prefixLift 3922994
  have htrace : WordTrace (prefixWord ++ tailWord_3922994) baseStart_3922994 baseEnd_3922994 := by
    simpa [prefixWord, tailWord_3922994, baseEnd_3922994] using wordTrace_append hprefix tailTrace_3922994
  have hstable : (prefixWord ++ tailWord_3922994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3922994).length < 2 ^ (prefixWord ++ tailWord_3922994).sum := by decide
  have hdescent : baseEnd_3922994 < baseStart_3922994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3922994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923067 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 3]
def baseStart_3923067 : Nat := 118140960795 + 3923067 * 2 ^ 59
def prefixEnd_3923067 : Nat := 4983230072969 + 3 ^ 40 * 3923067 * 2
def baseEnd_3923067 : Nat := 2014419010792107716020649

theorem tailTrace_3923067 : CollatzResearch.WordTrace tailWord_3923067 prefixEnd_3923067 2014419010792107716020649 := by
  unfold tailWord_3923067
  simp only [CollatzResearch.WordTrace]
  refine ⟨143086008478405740346767455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95390672318937160231178303 143086008478405740346767455)
  ·
    refine ⟨214629012717608610520151183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143086008478405740346767455 214629012717608610520151183)
    ·
      refine ⟨321943519076412915780226775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214629012717608610520151183 321943519076412915780226775)
      ·
        refine ⟨482915278614619373670340163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321943519076412915780226775 482915278614619373670340163)
        ·
          refine ⟨724372917921929060505510245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482915278614619373670340163 724372917921929060505510245)
          ·
            refine ⟨135819922110361698844783171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 724372917921929060505510245 135819922110361698844783171)
            ·
              refine ⟨203729883165542548267174757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135819922110361698844783171 203729883165542548267174757)
              ·
                refine ⟨38199353093539227800095267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203729883165542548267174757 38199353093539227800095267)
                ·
                  refine ⟨57299029640308841700142901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38199353093539227800095267 57299029640308841700142901)
                  ·
                    refine ⟨5371784028778953909388397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57299029640308841700142901 5371784028778953909388397)
                    ·
                      refine ⟨2014419010792107716020649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371784028778953909388397 2014419010792107716020649)
                      ·
                        rfl

theorem cell23_3923067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5, 3].length) (baseStart_3923067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923067 prefixEnd_3923067 := by exact prefixLift 3923067
  have htrace : WordTrace (prefixWord ++ tailWord_3923067) baseStart_3923067 baseEnd_3923067 := by
    simpa [prefixWord, tailWord_3923067, baseEnd_3923067] using wordTrace_append hprefix tailTrace_3923067
  have hstable : (prefixWord ++ tailWord_3923067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923067).length < 2 ^ (prefixWord ++ tailWord_3923067).sum := by decide
  have hdescent : baseEnd_3923067 < baseStart_3923067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923102 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_3923102 : Nat := 118140960795 + 3923102 * 2 ^ 59
def prefixEnd_3923102 : Nat := 4983230072969 + 3 ^ 40 * 3923102 * 2
def baseEnd_3923102 : Nat := 2014436982615015079082989

theorem tailTrace_3923102 : CollatzResearch.WordTrace tailWord_3923102 prefixEnd_3923102 2014436982615015079082989 := by
  unfold tailWord_3923102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17885910629159867665536445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95391523355519294216194373 17885910629159867665536445)
  ·
    refine ⟨6707216485934950374576167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17885910629159867665536445 6707216485934950374576167)
    ·
      refine ⟨10060824728902425561864251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6707216485934950374576167 10060824728902425561864251)
      ·
        refine ⟨15091237093353638342796377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10060824728902425561864251 15091237093353638342796377)
        ·
          refine ⟨11318427820015228757097283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15091237093353638342796377 11318427820015228757097283)
          ·
            refine ⟨16977641730022843135645925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11318427820015228757097283 16977641730022843135645925)
            ·
              refine ⟨3183307824379283087933611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16977641730022843135645925 3183307824379283087933611)
              ·
                refine ⟨4774961736568924631900417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183307824379283087933611 4774961736568924631900417)
                ·
                  refine ⟨3581221302426693473925313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774961736568924631900417 3581221302426693473925313)
                  ·
                    refine ⟨2685915976820020105443985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581221302426693473925313 2685915976820020105443985)
                    ·
                      refine ⟨2014436982615015079082989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2685915976820020105443985 2014436982615015079082989)
                      ·
                        rfl

theorem cell23_3923102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_3923102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923102 prefixEnd_3923102 := by exact prefixLift 3923102
  have htrace : WordTrace (prefixWord ++ tailWord_3923102) baseStart_3923102 baseEnd_3923102 := by
    simpa [prefixWord, tailWord_3923102, baseEnd_3923102] using wordTrace_append hprefix tailTrace_3923102
  have hstable : (prefixWord ++ tailWord_3923102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923102).length < 2 ^ (prefixWord ++ tailWord_3923102).sum := by decide
  have hdescent : baseEnd_3923102 < baseStart_3923102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923107 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3923107 : Nat := 118140960795 + 3923107 * 2 ^ 59
def prefixEnd_3923107 : Nat := 4983230072969 + 3 ^ 40 * 3923107 * 2
def baseEnd_3923107 : Nat := 2014439550018287559520465

theorem tailTrace_3923107 : CollatzResearch.WordTrace tailWord_3923107 prefixEnd_3923107 2014439550018287559520465 := by
  unfold tailWord_3923107
  simp only [CollatzResearch.WordTrace]
  refine ⟨143087467398260827178223575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95391644932173884785482383 143087467398260827178223575)
  ·
    refine ⟨214631201097391240767335363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143087467398260827178223575 214631201097391240767335363)
    ·
      refine ⟨321946801646086861151003045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214631201097391240767335363 321946801646086861151003045)
      ·
        refine ⟨60365025308641286465813071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321946801646086861151003045 60365025308641286465813071)
        ·
          refine ⟨90547537962961929698719607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60365025308641286465813071 90547537962961929698719607)
          ·
            refine ⟨135821306944442894548079411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90547537962961929698719607 135821306944442894548079411)
            ·
              refine ⟨203731960416664341822119117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135821306944442894548079411 203731960416664341822119117)
              ·
                refine ⟨76399485156249128183294669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203731960416664341822119117 76399485156249128183294669)
                ·
                  refine ⟨28649806933593423068735501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76399485156249128183294669 28649806933593423068735501)
                  ·
                    refine ⟨10743677600097533650775813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28649806933593423068735501 10743677600097533650775813)
                    ·
                      refine ⟨2014439550018287559520465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10743677600097533650775813 2014439550018287559520465)
                      ·
                        rfl

theorem cell23_3923107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3923107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923107 prefixEnd_3923107 := by exact prefixLift 3923107
  have htrace : WordTrace (prefixWord ++ tailWord_3923107) baseStart_3923107 baseEnd_3923107 := by
    simpa [prefixWord, tailWord_3923107, baseEnd_3923107] using wordTrace_append hprefix tailTrace_3923107
  have hstable : (prefixWord ++ tailWord_3923107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923107).length < 2 ^ (prefixWord ++ tailWord_3923107).sum := by decide
  have hdescent : baseEnd_3923107 < baseStart_3923107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923121 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 2, 5]
def baseStart_3923121 : Nat := 118140960795 + 3923121 * 2 ^ 59
def prefixEnd_3923121 : Nat := 4983230072969 + 3 ^ 40 * 3923121 * 2
def baseEnd_3923121 : Nat := 671482246249150168248467

theorem tailTrace_3923121 : CollatzResearch.WordTrace tailWord_3923121 prefixEnd_3923121 671482246249150168248467 := by
  unfold tailWord_3923121
  simp only [CollatzResearch.WordTrace]
  refine ⟨143087978020210107569233217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95391985346806738379488811 143087978020210107569233217)
  ·
    refine ⟨107315983515157580676924913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143087978020210107569233217 107315983515157580676924913)
    ·
      refine ⟨80486987636368185507693685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107315983515157580676924913 80486987636368185507693685)
      ·
        refine ⟨7545655090909517391346283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80486987636368185507693685 7545655090909517391346283)
        ·
          refine ⟨11318482636364276087019425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545655090909517391346283 11318482636364276087019425)
          ·
            refine ⟨8488861977273207065264569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11318482636364276087019425 8488861977273207065264569)
            ·
              refine ⟨6366646482954905298948427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8488861977273207065264569 6366646482954905298948427)
              ·
                refine ⟨9549969724432357948422641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366646482954905298948427 9549969724432357948422641)
                ·
                  refine ⟨7162477293324268461316981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9549969724432357948422641 7162477293324268461316981)
                  ·
                    refine ⟨671482246249150168248467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7162477293324268461316981 671482246249150168248467)
                    ·
                      rfl

theorem cell23_3923121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_3923121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923121 prefixEnd_3923121 := by exact prefixLift 3923121
  have htrace : WordTrace (prefixWord ++ tailWord_3923121) baseStart_3923121 baseEnd_3923121 := by
    simpa [prefixWord, tailWord_3923121, baseEnd_3923121] using wordTrace_append hprefix tailTrace_3923121
  have hstable : (prefixWord ++ tailWord_3923121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923121).length < 2 ^ (prefixWord ++ tailWord_3923121).sum := by decide
  have hdescent : baseEnd_3923121 < baseStart_3923121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923142 : List Nat := [6, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3923142 : Nat := 118140960795 + 3923142 * 2 ^ 59
def prefixEnd_3923142 : Nat := 4983230072969 + 3 ^ 40 * 3923142 * 2
def baseEnd_3923142 : Nat := 223828613537910546953645

theorem tailTrace_3923142 : CollatzResearch.WordTrace tailWord_3923142 prefixEnd_3923142 223828613537910546953645 := by
  unfold tailWord_3923142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471523248535438379867115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95392495968756018770498453 4471523248535438379867115)
  ·
    refine ⟨6707284872803157569800673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4471523248535438379867115 6707284872803157569800673)
    ·
      refine ⟨5030463654602368177350505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6707284872803157569800673 5030463654602368177350505)
      ·
        refine ⟨3772847740951776133012879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5030463654602368177350505 3772847740951776133012879)
        ·
          refine ⟨5659271611427664199519319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772847740951776133012879 5659271611427664199519319)
          ·
            refine ⟨8488907417141496299278979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5659271611427664199519319 8488907417141496299278979)
            ·
              refine ⟨12733361125712244448918469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488907417141496299278979 12733361125712244448918469)
              ·
                refine ⟨2387505211071045834172213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12733361125712244448918469 2387505211071045834172213)
                ·
                  refine ⟨223828613537910546953645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2387505211071045834172213 223828613537910546953645)
                  ·
                    rfl

theorem cell23_3923142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3923142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923142 prefixEnd_3923142 := by exact prefixLift 3923142
  have htrace : WordTrace (prefixWord ++ tailWord_3923142) baseStart_3923142 baseEnd_3923142 := by
    simpa [prefixWord, tailWord_3923142, baseEnd_3923142] using wordTrace_append hprefix tailTrace_3923142
  have hstable : (prefixWord ++ tailWord_3923142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923142).length < 2 ^ (prefixWord ++ tailWord_3923142).sum := by decide
  have hdescent : baseEnd_3923142 < baseStart_3923142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923175 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3923175 : Nat := 118140960795 + 3923175 * 2 ^ 59
def prefixEnd_3923175 : Nat := 4983230072969 + 3 ^ 40 * 3923175 * 2
def baseEnd_3923175 : Nat := 2014474466702793293470153

theorem tailTrace_3923175 : CollatzResearch.WordTrace tailWord_3923175 prefixEnd_3923175 2014474466702793293470153 := by
  unfold tailWord_3923175
  simp only [CollatzResearch.WordTrace]
  refine ⟨143089947562014474791698979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95393298374676316527799319 143089947562014474791698979)
  ·
    refine ⟨214634921343021712187548469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143089947562014474791698979 214634921343021712187548469)
    ·
      refine ⟨20122023875908285517582669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214634921343021712187548469 20122023875908285517582669)
      ·
        refine ⟨7545758953465607069093501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20122023875908285517582669 7545758953465607069093501)
        ·
          refine ⟨2829659607549602650910063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7545758953465607069093501 2829659607549602650910063)
          ·
            refine ⟨4244489411324403976365095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829659607549602650910063 4244489411324403976365095)
            ·
              refine ⟨6366734116986605964547643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244489411324403976365095 6366734116986605964547643)
              ·
                refine ⟨9550101175479908946821465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366734116986605964547643 9550101175479908946821465)
                ·
                  refine ⟨7162575881609931710116099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9550101175479908946821465 7162575881609931710116099)
                  ·
                    refine ⟨10743863822414897565174149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7162575881609931710116099 10743863822414897565174149)
                    ·
                      refine ⟨2014474466702793293470153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10743863822414897565174149 2014474466702793293470153)
                      ·
                        rfl

theorem cell23_3923175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3923175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923175 prefixEnd_3923175 := by exact prefixLift 3923175
  have htrace : WordTrace (prefixWord ++ tailWord_3923175) baseStart_3923175 baseEnd_3923175 := by
    simpa [prefixWord, tailWord_3923175, baseEnd_3923175] using wordTrace_append hprefix tailTrace_3923175
  have hstable : (prefixWord ++ tailWord_3923175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923175).length < 2 ^ (prefixWord ++ tailWord_3923175).sum := by decide
  have hdescent : baseEnd_3923175 < baseStart_3923175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923178 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_3923178 : Nat := 118140960795 + 3923178 * 2 ^ 59
def prefixEnd_3923178 : Nat := 4983230072969 + 3 ^ 40 * 3923178 * 2
def baseEnd_3923178 : Nat := 2014476007144756781732639

theorem tailTrace_3923178 : CollatzResearch.WordTrace tailWord_3923178 prefixEnd_3923178 2014476007144756781732639 := by
  unfold tailWord_3923178
  simp only [CollatzResearch.WordTrace]
  refine ⟨35772514245250901576014547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95393371320669070869372125 35772514245250901576014547)
  ·
    refine ⟨53658771367876352364021821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35772514245250901576014547 53658771367876352364021821)
    ·
      refine ⟨20122039262953632136508183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53658771367876352364021821 20122039262953632136508183)
      ·
        refine ⟨30183058894430448204762275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20122039262953632136508183 30183058894430448204762275)
        ·
          refine ⟨45274588341645672307143413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30183058894430448204762275 45274588341645672307143413)
          ·
            refine ⟨4244492657029281778794695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45274588341645672307143413 4244492657029281778794695)
            ·
              refine ⟨6366738985543922668192043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244492657029281778794695 6366738985543922668192043)
              ·
                refine ⟨9550108478315884002288065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366738985543922668192043 9550108478315884002288065)
                ·
                  refine ⟨7162581358736913001716049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9550108478315884002288065 7162581358736913001716049)
                  ·
                    refine ⟨5371936019052684751287037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7162581358736913001716049 5371936019052684751287037)
                    ·
                      refine ⟨2014476007144756781732639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5371936019052684751287037 2014476007144756781732639)
                      ·
                        rfl

theorem cell23_3923178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_3923178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923178 prefixEnd_3923178 := by exact prefixLift 3923178
  have htrace : WordTrace (prefixWord ++ tailWord_3923178) baseStart_3923178 baseEnd_3923178 := by
    simpa [prefixWord, tailWord_3923178, baseEnd_3923178] using wordTrace_append hprefix tailTrace_3923178
  have hstable : (prefixWord ++ tailWord_3923178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923178).length < 2 ^ (prefixWord ++ tailWord_3923178).sum := by decide
  have hdescent : baseEnd_3923178 < baseStart_3923178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923198 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_3923198 : Nat := 118140960795 + 3923198 * 2 ^ 59
def prefixEnd_3923198 : Nat := 4983230072969 + 3 ^ 40 * 3923198 * 2
def baseEnd_3923198 : Nat := 223831808528649633720283

theorem tailTrace_3923198 : CollatzResearch.WordTrace tailWord_3923198 prefixEnd_3923198 223831808528649633720283 := by
  unfold tailWord_3923198
  simp only [CollatzResearch.WordTrace]
  refine ⟨17886348305116393714973281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95393857627287433146524165 17886348305116393714973281)
  ·
    refine ⟨13414761228837295286229961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17886348305116393714973281 13414761228837295286229961)
    ·
      refine ⟨10061070921627971464672471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13414761228837295286229961 10061070921627971464672471)
      ·
        refine ⟨15091606382441957197008707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061070921627971464672471 15091606382441957197008707)
        ·
          refine ⟨22637409573662935795513061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15091606382441957197008707 22637409573662935795513061)
          ·
            refine ⟨4244514295061800461658699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22637409573662935795513061 4244514295061800461658699)
            ·
              refine ⟨6366771442592700692488049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244514295061800461658699 6366771442592700692488049)
              ·
                refine ⟨4775078581944525519366037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366771442592700692488049 4775078581944525519366037)
                ·
                  refine ⟨223831808528649633720283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4775078581944525519366037 223831808528649633720283)
                  ·
                    rfl

theorem cell23_3923198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_3923198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923198 prefixEnd_3923198 := by exact prefixLift 3923198
  have htrace : WordTrace (prefixWord ++ tailWord_3923198) baseStart_3923198 baseEnd_3923198 := by
    simpa [prefixWord, tailWord_3923198, baseEnd_3923198] using wordTrace_append hprefix tailTrace_3923198
  have hstable : (prefixWord ++ tailWord_3923198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923198).length < 2 ^ (prefixWord ++ tailWord_3923198).sum := by decide
  have hdescent : baseEnd_3923198 < baseStart_3923198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923242 : List Nat := [3, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3923242 : Nat := 118140960795 + 3923242 * 2 ^ 59
def prefixEnd_3923242 : Nat := 4983230072969 + 3 ^ 40 * 3923242 * 2
def baseEnd_3923242 : Nat := 2014508869906644531332345

theorem tailTrace_3923242 : CollatzResearch.WordTrace tailWord_3923242 prefixEnd_3923242 2014508869906644531332345 := by
  unfold tailWord_3923242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35773097813192936308596995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95394927501847830156258653 35773097813192936308596995)
  ·
    refine ⟨53659646719789404462895493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35773097813192936308596995 53659646719789404462895493)
    ·
      refine ⟨10061183759960513336792905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53659646719789404462895493 10061183759960513336792905)
      ·
        refine ⟨7545887819970385002594679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10061183759960513336792905 7545887819970385002594679)
        ·
          refine ⟨11318831729955577503892019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545887819970385002594679 11318831729955577503892019)
          ·
            refine ⟨16978247594933366255838029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11318831729955577503892019 16978247594933366255838029)
            ·
              refine ⟨6366842848100012345939261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16978247594933366255838029 6366842848100012345939261)
              ·
                refine ⟨2387566068037504629727223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6366842848100012345939261 2387566068037504629727223)
                ·
                  refine ⟨3581349102056256944590835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387566068037504629727223 3581349102056256944590835)
                  ·
                    refine ⟨5372023653084385416886253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3581349102056256944590835 5372023653084385416886253)
                    ·
                      refine ⟨2014508869906644531332345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5372023653084385416886253 2014508869906644531332345)
                      ·
                        rfl

theorem cell23_3923242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3923242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923242 prefixEnd_3923242 := by exact prefixLift 3923242
  have htrace : WordTrace (prefixWord ++ tailWord_3923242) baseStart_3923242 baseEnd_3923242 := by
    simpa [prefixWord, tailWord_3923242, baseEnd_3923242] using wordTrace_append hprefix tailTrace_3923242
  have hstable : (prefixWord ++ tailWord_3923242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923242).length < 2 ^ (prefixWord ++ tailWord_3923242).sum := by decide
  have hdescent : baseEnd_3923242 < baseStart_3923242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923244 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 4]
def baseStart_3923244 : Nat := 118140960795 + 3923244 * 2 ^ 59
def prefixEnd_3923244 : Nat := 4983230072969 + 3 ^ 40 * 3923244 * 2
def baseEnd_3923244 : Nat := 2014509896867953523507335

theorem tailTrace_3923244 : CollatzResearch.WordTrace tailWord_3923244 prefixEnd_3923244 2014509896867953523507335 := by
  unfold tailWord_3923244
  simp only [CollatzResearch.WordTrace]
  refine ⟨71546232099382249787980393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95394976132509666383973857 71546232099382249787980393)
  ·
    refine ⟨53659674074536687340985295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71546232099382249787980393 53659674074536687340985295)
    ·
      refine ⟨80489511111805031011477943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53659674074536687340985295 80489511111805031011477943)
      ·
        refine ⟨120734266667707546517216915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80489511111805031011477943 120734266667707546517216915)
        ·
          refine ⟨181101400001561319775825373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120734266667707546517216915 181101400001561319775825373)
          ·
            refine ⟨67913025000585494915934515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181101400001561319775825373 67913025000585494915934515)
            ·
              refine ⟨101869537500878242373901773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67913025000585494915934515 101869537500878242373901773)
              ·
                refine ⟨38201076562829340890213165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101869537500878242373901773 38201076562829340890213165)
                ·
                  refine ⟨14325403711061002833829937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38201076562829340890213165 14325403711061002833829937)
                  ·
                    refine ⟨10744052783295752125372453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14325403711061002833829937 10744052783295752125372453)
                    ·
                      refine ⟨2014509896867953523507335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10744052783295752125372453 2014509896867953523507335)
                      ·
                        rfl

theorem cell23_3923244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_3923244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923244 prefixEnd_3923244 := by exact prefixLift 3923244
  have htrace : WordTrace (prefixWord ++ tailWord_3923244) baseStart_3923244 baseEnd_3923244 := by
    simpa [prefixWord, tailWord_3923244, baseEnd_3923244] using wordTrace_append hprefix tailTrace_3923244
  have hstable : (prefixWord ++ tailWord_3923244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923244).length < 2 ^ (prefixWord ++ tailWord_3923244).sum := by decide
  have hdescent : baseEnd_3923244 < baseStart_3923244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923251 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 5]
def baseStart_3923251 : Nat := 118140960795 + 3923251 * 2 ^ 59
def prefixEnd_3923251 : Nat := 4983230072969 + 3 ^ 40 * 3923251 * 2
def baseEnd_3923251 : Nat := 2014513491232534996119803

theorem tailTrace_3923251 : CollatzResearch.WordTrace tailWord_3923251 prefixEnd_3923251 2014513491232534996119803 := by
  unfold tailWord_3923251
  simp only [CollatzResearch.WordTrace]
  refine ⟨143092719509739139771465607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95395146339826093180977071 143092719509739139771465607)
  ·
    refine ⟨214639079264608709657198411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143092719509739139771465607 214639079264608709657198411)
    ·
      refine ⟨321958618896913064485797617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214639079264608709657198411 321958618896913064485797617)
      ·
        refine ⟨241468964172684798364348213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321958618896913064485797617 241468964172684798364348213)
        ·
          refine ⟨22637715391189199846657645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241468964172684798364348213 22637715391189199846657645)
          ·
            refine ⟨8489143271695949942496617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22637715391189199846657645 8489143271695949942496617)
            ·
              refine ⟨6366857453771962456872463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489143271695949942496617 6366857453771962456872463)
              ·
                refine ⟨9550286180657943685308695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366857453771962456872463 9550286180657943685308695)
                ·
                  refine ⟨14325429270986915527963043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9550286180657943685308695 14325429270986915527963043)
                  ·
                    refine ⟨21488143906480373291944565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14325429270986915527963043 21488143906480373291944565)
                    ·
                      refine ⟨2014513491232534996119803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21488143906480373291944565 2014513491232534996119803)
                      ·
                        rfl

theorem cell23_3923251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_3923251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923251 prefixEnd_3923251 := by exact prefixLift 3923251
  have htrace : WordTrace (prefixWord ++ tailWord_3923251) baseStart_3923251 baseEnd_3923251 := by
    simpa [prefixWord, tailWord_3923251, baseEnd_3923251] using wordTrace_append hprefix tailTrace_3923251
  have hstable : (prefixWord ++ tailWord_3923251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923251).length < 2 ^ (prefixWord ++ tailWord_3923251).sum := by decide
  have hdescent : baseEnd_3923251 < baseStart_3923251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923268 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3923268 : Nat := 118140960795 + 3923268 * 2 ^ 59
def prefixEnd_3923268 : Nat := 4983230072969 + 3 ^ 40 * 3923268 * 2
def baseEnd_3923268 : Nat := 2014522220403661429607225

theorem tailTrace_3923268 : CollatzResearch.WordTrace tailWord_3923268 prefixEnd_3923268 2014522220403661429607225 := by
  unfold tailWord_3923268
  simp only [CollatzResearch.WordTrace]
  refine ⟨71546669775338775837417229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95395559700451701116556305 71546669775338775837417229)
  ·
    refine ⟨26830001165752040939031461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71546669775338775837417229 26830001165752040939031461)
    ·
      refine ⟨5030625218578507676068399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26830001165752040939031461 5030625218578507676068399)
      ·
        refine ⟨7545937827867761514102599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5030625218578507676068399 7545937827867761514102599)
        ·
          refine ⟨11318906741801642271153899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545937827867761514102599 11318906741801642271153899)
          ·
            refine ⟨16978360112702463406730849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11318906741801642271153899 16978360112702463406730849)
            ·
              refine ⟨12733770084526847555048137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16978360112702463406730849 12733770084526847555048137)
              ·
                refine ⟨9550327563395135666286103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12733770084526847555048137 9550327563395135666286103)
                ·
                  refine ⟨14325491345092703499429155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9550327563395135666286103 14325491345092703499429155)
                  ·
                    refine ⟨21488237017639055249143733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14325491345092703499429155 21488237017639055249143733)
                    ·
                      refine ⟨2014522220403661429607225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21488237017639055249143733 2014522220403661429607225)
                      ·
                        rfl

theorem cell23_3923268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3923268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923268 prefixEnd_3923268 := by exact prefixLift 3923268
  have htrace : WordTrace (prefixWord ++ tailWord_3923268) baseStart_3923268 baseEnd_3923268 := by
    simpa [prefixWord, tailWord_3923268, baseEnd_3923268] using wordTrace_append hprefix tailTrace_3923268
  have hstable : (prefixWord ++ tailWord_3923268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923268).length < 2 ^ (prefixWord ++ tailWord_3923268).sum := by decide
  have hdescent : baseEnd_3923268 < baseStart_3923268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923281 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_3923281 : Nat := 118140960795 + 3923281 * 2 ^ 59
def prefixEnd_3923281 : Nat := 4983230072969 + 3 ^ 40 * 3923281 * 2
def baseEnd_3923281 : Nat := 2014528895652169878744665

theorem tailTrace_3923281 : CollatzResearch.WordTrace tailWord_3923281 prefixEnd_3923281 2014528895652169878744665 := by
  unfold tailWord_3923281
  simp only [CollatzResearch.WordTrace]
  refine ⟨143093813699630454895057697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95395875799753636596705131 143093813699630454895057697)
  ·
    refine ⟨107320360274722841171293273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143093813699630454895057697 107320360274722841171293273)
    ·
      refine ⟨80490270206042130878469955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107320360274722841171293273 80490270206042130878469955)
      ·
        refine ⟨120735405309063196317704933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80490270206042130878469955 120735405309063196317704933)
        ·
          refine ⟨22637888495449349309569675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120735405309063196317704933 22637888495449349309569675)
          ·
            refine ⟨33956832743174023964354513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22637888495449349309569675 33956832743174023964354513)
            ·
              refine ⟨25467624557380517973265885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33956832743174023964354513 25467624557380517973265885)
              ·
                refine ⟨9550359209017694239974707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25467624557380517973265885 9550359209017694239974707)
                ·
                  refine ⟨14325538813526541359962061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9550359209017694239974707 14325538813526541359962061)
                  ·
                    refine ⟨5372077055072453009985773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14325538813526541359962061 5372077055072453009985773)
                    ·
                      refine ⟨2014528895652169878744665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5372077055072453009985773 2014528895652169878744665)
                      ·
                        rfl

theorem cell23_3923281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_3923281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923281 prefixEnd_3923281 := by exact prefixLift 3923281
  have htrace : WordTrace (prefixWord ++ tailWord_3923281) baseStart_3923281 baseEnd_3923281 := by
    simpa [prefixWord, tailWord_3923281, baseEnd_3923281] using wordTrace_append hprefix tailTrace_3923281
  have hstable : (prefixWord ++ tailWord_3923281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923281).length < 2 ^ (prefixWord ++ tailWord_3923281).sum := by decide
  have hdescent : baseEnd_3923281 < baseStart_3923281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923285 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3923285 : Nat := 118140960795 + 3923285 * 2 ^ 59
def prefixEnd_3923285 : Nat := 4983230072969 + 3 ^ 40 * 3923285 * 2
def baseEnd_3923285 : Nat := 2014530949574787863094647

theorem tailTrace_3923285 : CollatzResearch.WordTrace tailWord_3923285 prefixEnd_3923285 2014530949574787863094647 := by
  unfold tailWord_3923285
  simp only [CollatzResearch.WordTrace]
  refine ⟨143093959591615963578203309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95395973061077309052135539 143093959591615963578203309)
  ·
    refine ⟨53660234846855986341826241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143093959591615963578203309 53660234846855986341826241)
    ·
      refine ⟨40245176135141989756369681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53660234846855986341826241 40245176135141989756369681)
      ·
        refine ⟨30183882101356492317277261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40245176135141989756369681 30183882101356492317277261)
        ·
          refine ⟨11318955788008684618978973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30183882101356492317277261 11318955788008684618978973)
          ·
            refine ⟨4244608420503256732117115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11318955788008684618978973 4244608420503256732117115)
            ·
              refine ⟨6366912630754885098175673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244608420503256732117115 6366912630754885098175673)
              ·
                refine ⟨4775184473066163823631755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366912630754885098175673 4775184473066163823631755)
                ·
                  refine ⟨7162776709599245735447633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775184473066163823631755 7162776709599245735447633)
                  ·
                    refine ⟨5372082532199434301585725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7162776709599245735447633 5372082532199434301585725)
                    ·
                      refine ⟨2014530949574787863094647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5372082532199434301585725 2014530949574787863094647)
                      ·
                        rfl

theorem cell23_3923285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3923285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923285 prefixEnd_3923285 := by exact prefixLift 3923285
  have htrace : WordTrace (prefixWord ++ tailWord_3923285) baseStart_3923285 baseEnd_3923285 := by
    simpa [prefixWord, tailWord_3923285, baseEnd_3923285] using wordTrace_append hprefix tailTrace_3923285
  have hstable : (prefixWord ++ tailWord_3923285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923285).length < 2 ^ (prefixWord ++ tailWord_3923285).sum := by decide
  have hdescent : baseEnd_3923285 < baseStart_3923285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923286 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3923286 : Nat := 118140960795 + 3923286 * 2 ^ 59
def prefixEnd_3923286 : Nat := 4983230072969 + 3 ^ 40 * 3923286 * 2
def baseEnd_3923286 : Nat := 2014531463055442359182143

theorem tailTrace_3923286 : CollatzResearch.WordTrace tailWord_3923286 prefixEnd_3923286 2014531463055442359182143 := by
  unfold tailWord_3923286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8943374754038271296811857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95395997376408227165993141 8943374754038271296811857)
  ·
    refine ⟨6707531065528703472608893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8943374754038271296811857 6707531065528703472608893)
    ·
      refine ⟨2515324149573263802228335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6707531065528703472608893 2515324149573263802228335)
      ·
        refine ⟨3772986224359895703342503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515324149573263802228335 3772986224359895703342503)
        ·
          refine ⟨5659479336539843555013755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772986224359895703342503 5659479336539843555013755)
          ·
            refine ⟨8489219004809765332520633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5659479336539843555013755 8489219004809765332520633)
            ·
              refine ⟨6366914253607323999390475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489219004809765332520633 6366914253607323999390475)
              ·
                refine ⟨9550371380410985999085713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6366914253607323999390475 9550371380410985999085713)
                ·
                  refine ⟨7162778535308239499314285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9550371380410985999085713 7162778535308239499314285)
                  ·
                    refine ⟨2686041950740589812242857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7162778535308239499314285 2686041950740589812242857)
                    ·
                      refine ⟨2014531463055442359182143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686041950740589812242857 2014531463055442359182143)
                      ·
                        rfl

theorem cell23_3923286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3923286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923286 prefixEnd_3923286 := by exact prefixLift 3923286
  have htrace : WordTrace (prefixWord ++ tailWord_3923286) baseStart_3923286 baseEnd_3923286 := by
    simpa [prefixWord, tailWord_3923286, baseEnd_3923286] using wordTrace_append hprefix tailTrace_3923286
  have hstable : (prefixWord ++ tailWord_3923286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923286).length < 2 ^ (prefixWord ++ tailWord_3923286).sum := by decide
  have hdescent : baseEnd_3923286 < baseStart_3923286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923298 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3923298 : Nat := 118140960795 + 3923298 * 2 ^ 59
def prefixEnd_3923298 : Nat := 4983230072969 + 3 ^ 40 * 3923298 * 2
def baseEnd_3923298 : Nat := 2014537624823296312232087

theorem tailTrace_3923298 : CollatzResearch.WordTrace tailWord_3923298 prefixEnd_3923298 2014537624823296312232087 := by
  unfold tailWord_3923298
  simp only [CollatzResearch.WordTrace]
  refine ⟨35773608435142216699606637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95396289160379244532284365 35773608435142216699606637)
  ·
    refine ⟨13415103163178331262352489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35773608435142216699606637 13415103163178331262352489)
    ·
      refine ⟨10061327372383748446764367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13415103163178331262352489 10061327372383748446764367)
      ·
        refine ⟨15091991058575622670146551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061327372383748446764367 15091991058575622670146551)
        ·
          refine ⟨22637986587863434005219827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15091991058575622670146551 22637986587863434005219827)
          ·
            refine ⟨33956979881795151007829741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22637986587863434005219827 33956979881795151007829741)
            ·
              refine ⟨12733867455673181627936153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33956979881795151007829741 12733867455673181627936153)
              ·
                refine ⟨9550400591754886220952115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12733867455673181627936153 9550400591754886220952115)
                ·
                  refine ⟨14325600887632329331428173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9550400591754886220952115 14325600887632329331428173)
                  ·
                    refine ⟨5372100332862123499285565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14325600887632329331428173 5372100332862123499285565)
                    ·
                      refine ⟨2014537624823296312232087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5372100332862123499285565 2014537624823296312232087)
                      ·
                        rfl

theorem cell23_3923298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3923298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923298 prefixEnd_3923298 := by exact prefixLift 3923298
  have htrace : WordTrace (prefixWord ++ tailWord_3923298) baseStart_3923298 baseEnd_3923298 := by
    simpa [prefixWord, tailWord_3923298, baseEnd_3923298] using wordTrace_append hprefix tailTrace_3923298
  have hstable : (prefixWord ++ tailWord_3923298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923298).length < 2 ^ (prefixWord ++ tailWord_3923298).sum := by decide
  have hdescent : baseEnd_3923298 < baseStart_3923298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923331 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 2, 6]
def baseStart_3923331 : Nat := 118140960795 + 3923331 * 2 ^ 59
def prefixEnd_3923331 : Nat := 4983230072969 + 3 ^ 40 * 3923331 * 2
def baseEnd_3923331 : Nat := 671518189894964894373145

theorem tailTrace_3923331 : CollatzResearch.WordTrace tailWord_3923331 prefixEnd_3923331 671518189894964894373145 := by
  unfold tailWord_3923331
  simp only [CollatzResearch.WordTrace]
  refine ⟨143095637349449313434377847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95397091566299542289585231 143095637349449313434377847)
  ·
    refine ⟨214643456024173970151566771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143095637349449313434377847 214643456024173970151566771)
    ·
      refine ⟨321965184036260955227350157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214643456024173970151566771 321965184036260955227350157)
      ·
        refine ⟨120736944013597858210256309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321965184036260955227350157 120736944013597858210256309)
        ·
          refine ⟨11319088501274799207211529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120736944013597858210256309 11319088501274799207211529)
          ·
            refine ⟨8489316375956099405408647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11319088501274799207211529 8489316375956099405408647)
            ·
              refine ⟨12733974563934149108112971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8489316375956099405408647 12733974563934149108112971)
              ·
                refine ⟨19100961845901223662169457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12733974563934149108112971 19100961845901223662169457)
                ·
                  refine ⟨14325721384425917746627093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19100961845901223662169457 14325721384425917746627093)
                  ·
                    refine ⟨671518189894964894373145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14325721384425917746627093 671518189894964894373145)
                    ·
                      rfl

theorem cell23_3923331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 6].length) (baseStart_3923331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923331 prefixEnd_3923331 := by exact prefixLift 3923331
  have htrace : WordTrace (prefixWord ++ tailWord_3923331) baseStart_3923331 baseEnd_3923331 := by
    simpa [prefixWord, tailWord_3923331, baseEnd_3923331] using wordTrace_append hprefix tailTrace_3923331
  have hstable : (prefixWord ++ tailWord_3923331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923331).length < 2 ^ (prefixWord ++ tailWord_3923331).sum := by decide
  have hdescent : baseEnd_3923331 < baseStart_3923331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923412 : List Nat := [2, 4, 1, 2, 3, 2, 1, 3, 5]
def baseStart_3923412 : Nat := 118140960795 + 3923412 * 2 ^ 59
def prefixEnd_3923412 : Nat := 4983230072969 + 3 ^ 40 * 3923412 * 2
def baseEnd_3923412 : Nat := 223844017957545429578507

theorem tailTrace_3923412 : CollatzResearch.WordTrace tailWord_3923412 prefixEnd_3923412 223844017957545429578507 := by
  unfold tailWord_3923412
  simp only [CollatzResearch.WordTrace]
  refine ⟨71549295831077932134038245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95399061108103909512050993 71549295831077932134038245)
  ·
    refine ⟨13415492968327112275132171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71549295831077932134038245 13415492968327112275132171)
    ·
      refine ⟨20123239452490668412698257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13415492968327112275132171 20123239452490668412698257)
      ·
        refine ⟨15092429589368001309523693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20123239452490668412698257 15092429589368001309523693)
        ·
          refine ⟨5659661096013000491071385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15092429589368001309523693 5659661096013000491071385)
          ·
            refine ⟨4244745822009750368303539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5659661096013000491071385 4244745822009750368303539)
            ·
              refine ⟨6367118733014625552455309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244745822009750368303539 6367118733014625552455309)
              ·
                refine ⟨2387669524880484582170741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6367118733014625552455309 2387669524880484582170741)
                ·
                  refine ⟨223844017957545429578507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2387669524880484582170741 223844017957545429578507)
                  ·
                    rfl

theorem cell23_3923412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_3923412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923412 prefixEnd_3923412 := by exact prefixLift 3923412
  have htrace : WordTrace (prefixWord ++ tailWord_3923412) baseStart_3923412 baseEnd_3923412 := by
    simpa [prefixWord, tailWord_3923412, baseEnd_3923412] using wordTrace_append hprefix tailTrace_3923412
  have hstable : (prefixWord ++ tailWord_3923412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923412).length < 2 ^ (prefixWord ++ tailWord_3923412).sum := by decide
  have hdescent : baseEnd_3923412 < baseStart_3923412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923428 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_3923428 : Nat := 118140960795 + 3923428 * 2 ^ 59
def prefixEnd_3923428 : Nat := 4983230072969 + 3 ^ 40 * 3923428 * 2
def baseEnd_3923428 : Nat := 2014604377308380803606489

theorem tailTrace_3923428 : CollatzResearch.WordTrace tailWord_3923428 prefixEnd_3923428 2014604377308380803606489 := by
  unfold tailWord_3923428
  simp only [CollatzResearch.WordTrace]
  refine ⟨71549587615048949500329469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95399450153398599333772625 71549587615048949500329469)
  ·
    refine ⟨26831095355643356062623551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71549587615048949500329469 26831095355643356062623551)
    ·
      refine ⟨40246643033465034093935327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26831095355643356062623551 40246643033465034093935327)
      ·
        refine ⟨60369964550197551140902991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40246643033465034093935327 60369964550197551140902991)
        ·
          refine ⟨90554946825296326711354487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60369964550197551140902991 90554946825296326711354487)
          ·
            refine ⟨135832420237944490067031731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90554946825296326711354487 135832420237944490067031731)
            ·
              refine ⟨203748630356916735100547597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135832420237944490067031731 203748630356916735100547597)
              ·
                refine ⟨76405736383843775662705349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203748630356916735100547597 76405736383843775662705349)
                ·
                  refine ⟨14326075571970707936757253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76405736383843775662705349 14326075571970707936757253)
                  ·
                    refine ⟨2686139169744507738141985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14326075571970707936757253 2686139169744507738141985)
                    ·
                      refine ⟨2014604377308380803606489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686139169744507738141985 2014604377308380803606489)
                      ·
                        rfl

theorem cell23_3923428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_3923428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923428 prefixEnd_3923428 := by exact prefixLift 3923428
  have htrace : WordTrace (prefixWord ++ tailWord_3923428) baseStart_3923428 baseEnd_3923428 := by
    simpa [prefixWord, tailWord_3923428, baseEnd_3923428] using wordTrace_append hprefix tailTrace_3923428
  have hstable : (prefixWord ++ tailWord_3923428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923428).length < 2 ^ (prefixWord ++ tailWord_3923428).sum := by decide
  have hdescent : baseEnd_3923428 < baseStart_3923428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923451 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 6]
def baseStart_3923451 : Nat := 118140960795 + 3923451 * 2 ^ 59
def prefixEnd_3923451 : Nat := 4983230072969 + 3 ^ 40 * 3923451 * 2
def baseEnd_3923451 : Nat := 223846243040381579290987

theorem tailTrace_3923451 : CollatzResearch.WordTrace tailWord_3923451 prefixEnd_3923451 223846243040381579290987 := by
  unfold tailWord_3923451
  simp only [CollatzResearch.WordTrace]
  refine ⟨143100014109014573928746207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95400009406009715952497471 143100014109014573928746207)
  ·
    refine ⟨214650021163521860893119311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143100014109014573928746207 214650021163521860893119311)
    ·
      refine ⟨321975031745282791339678967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214650021163521860893119311 321975031745282791339678967)
      ·
        refine ⟨482962547617924187009518451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321975031745282791339678967 482962547617924187009518451)
        ·
          refine ⟨724443821426886280514277677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482962547617924187009518451 724443821426886280514277677)
          ·
            refine ⟨271666433035082355192854129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724443821426886280514277677 271666433035082355192854129)
            ·
              refine ⟨203749824776311766394640597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271666433035082355192854129 203749824776311766394640597)
              ·
                refine ⟨4775386518194807024874389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203749824776311766394640597 4775386518194807024874389)
                ·
                  refine ⟨223846243040381579290987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4775386518194807024874389 223846243040381579290987)
                  ·
                    rfl

theorem cell23_3923451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 6].length) (baseStart_3923451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923451 prefixEnd_3923451 := by exact prefixLift 3923451
  have htrace : WordTrace (prefixWord ++ tailWord_3923451) baseStart_3923451 baseEnd_3923451 := by
    simpa [prefixWord, tailWord_3923451, baseEnd_3923451] using wordTrace_append hprefix tailTrace_3923451
  have hstable : (prefixWord ++ tailWord_3923451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923451).length < 2 ^ (prefixWord ++ tailWord_3923451).sum := by decide
  have hdescent : baseEnd_3923451 < baseStart_3923451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923481 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 7, 5]
def baseStart_3923481 : Nat := 118140960795 + 3923481 * 2 ^ 59
def prefixEnd_3923481 : Nat := 4983230072969 + 3 ^ 40 * 3923481 * 2
def baseEnd_3923481 : Nat := 671543863927689698747915

theorem tailTrace_3923481 : CollatzResearch.WordTrace tailWord_3923481 prefixEnd_3923481 671543863927689698747915 := by
  unfold tailWord_3923481
  simp only [CollatzResearch.WordTrace]
  refine ⟨143101108298905889052338297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95400738865937259368225531 143101108298905889052338297)
  ·
    refine ⟨107325831224179416789253723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143101108298905889052338297 107325831224179416789253723)
    ·
      refine ⟨160988746836269125183880585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107325831224179416789253723 160988746836269125183880585)
      ·
        refine ⟨120741560127201843887910439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160988746836269125183880585 120741560127201843887910439)
        ·
          refine ⟨181112340190802765831865659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120741560127201843887910439 181112340190802765831865659)
          ·
            refine ⟨271668510286204148747798489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181112340190802765831865659 271668510286204148747798489)
            ·
              refine ⟨203751382714653111560848867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271668510286204148747798489 203751382714653111560848867)
              ·
                refine ⟨305627074071979667341273301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203751382714653111560848867 305627074071979667341273301)
                ·
                  refine ⟨7163134548562023453311093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305627074071979667341273301 7163134548562023453311093)
                  ·
                    refine ⟨671543863927689698747915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7163134548562023453311093 671543863927689698747915)
                    ·
                      rfl

theorem cell23_3923481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_3923481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923481 prefixEnd_3923481 := by exact prefixLift 3923481
  have htrace : WordTrace (prefixWord ++ tailWord_3923481) baseStart_3923481 baseEnd_3923481 := by
    simpa [prefixWord, tailWord_3923481, baseEnd_3923481] using wordTrace_append hprefix tailTrace_3923481
  have hstable : (prefixWord ++ tailWord_3923481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923481).length < 2 ^ (prefixWord ++ tailWord_3923481).sum := by decide
  have hdescent : baseEnd_3923481 < baseStart_3923481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923489 : List Nat := [1, 2, 3, 2, 2, 4, 2, 2, 1, 4]
def baseStart_3923489 : Nat := 118140960795 + 3923489 * 2 ^ 59
def prefixEnd_3923489 : Nat := 4983230072969 + 3 ^ 40 * 3923489 * 2
def baseEnd_3923489 : Nat := 671545233209435021647903

theorem tailTrace_3923489 : CollatzResearch.WordTrace tailWord_3923489 prefixEnd_3923489 671545233209435021647903 := by
  unfold tailWord_3923489
  simp only [CollatzResearch.WordTrace]
  refine ⟨143101400082876906418629521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95400933388584604279086347 143101400082876906418629521)
  ·
    refine ⟨107326050062157679813972141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143101400082876906418629521 107326050062157679813972141)
    ·
      refine ⟨40247268773309129930239553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107326050062157679813972141 40247268773309129930239553)
      ·
        refine ⟨30185451579981847447679665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40247268773309129930239553 30185451579981847447679665)
        ·
          refine ⟨22639088684986385585759749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30185451579981847447679665 22639088684986385585759749)
          ·
            refine ⟨4244829128434947297329953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22639088684986385585759749 4244829128434947297329953)
            ·
              refine ⟨3183621846326210472997465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244829128434947297329953 3183621846326210472997465)
              ·
                refine ⟨2387716384744657854748099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183621846326210472997465 2387716384744657854748099)
                ·
                  refine ⟨3581574577116986782122149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387716384744657854748099 3581574577116986782122149)
                  ·
                    refine ⟨671545233209435021647903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3581574577116986782122149 671545233209435021647903)
                    ·
                      rfl

theorem cell23_3923489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_3923489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923489 prefixEnd_3923489 := by exact prefixLift 3923489
  have htrace : WordTrace (prefixWord ++ tailWord_3923489) baseStart_3923489 baseEnd_3923489 := by
    simpa [prefixWord, tailWord_3923489, baseEnd_3923489] using wordTrace_append hprefix tailTrace_3923489
  have hstable : (prefixWord ++ tailWord_3923489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923489).length < 2 ^ (prefixWord ++ tailWord_3923489).sum := by decide
  have hdescent : baseEnd_3923489 < baseStart_3923489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923498 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3923498 : Nat := 118140960795 + 3923498 * 2 ^ 59
def prefixEnd_3923498 : Nat := 4983230072969 + 3 ^ 40 * 3923498 * 2
def baseEnd_3923498 : Nat := 671546773651398509910389

theorem tailTrace_3923498 : CollatzResearch.WordTrace tailWord_3923498 prefixEnd_3923498 671546773651398509910389 := by
  unfold tailWord_3923498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35775432084961075238926787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95401152226562867303804765 35775432084961075238926787)
  ·
    refine ⟨53663148127441612858390181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35775432084961075238926787 53663148127441612858390181)
    ·
      refine ⟨10061840273895302410948159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53663148127441612858390181 10061840273895302410948159)
      ·
        refine ⟨15092760410842953616422239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061840273895302410948159 15092760410842953616422239)
        ·
          refine ⟨22639140616264430424633359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15092760410842953616422239 22639140616264430424633359)
          ·
            refine ⟨33958710924396645636950039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22639140616264430424633359 33958710924396645636950039)
            ·
              refine ⟨50938066386594968455425059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33958710924396645636950039 50938066386594968455425059)
              ·
                refine ⟨76407099579892452683137589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50938066386594968455425059 76407099579892452683137589)
                ·
                  refine ⟨7163165585614917439044149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76407099579892452683137589 7163165585614917439044149)
                  ·
                    refine ⟨671546773651398509910389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7163165585614917439044149 671546773651398509910389)
                    ·
                      rfl

theorem cell23_3923498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3923498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923498 prefixEnd_3923498 := by exact prefixLift 3923498
  have htrace : WordTrace (prefixWord ++ tailWord_3923498) baseStart_3923498 baseEnd_3923498 := by
    simpa [prefixWord, tailWord_3923498, baseEnd_3923498] using wordTrace_append hprefix tailTrace_3923498
  have hstable : (prefixWord ++ tailWord_3923498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923498).length < 2 ^ (prefixWord ++ tailWord_3923498).sum := by decide
  have hdescent : baseEnd_3923498 < baseStart_3923498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923531 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6]
def baseStart_3923531 : Nat := 118140960795 + 3923531 * 2 ^ 59
def prefixEnd_3923531 : Nat := 4983230072969 + 3 ^ 40 * 3923531 * 2
def baseEnd_3923531 : Nat := 2014657265815793900618515

theorem tailTrace_3923531 : CollatzResearch.WordTrace tailWord_3923531 prefixEnd_3923531 2014657265815793900618515 := by
  unfold tailWord_3923531
  simp only [CollatzResearch.WordTrace]
  refine ⟨143102931948724747591658447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95401954632483165061105631 143102931948724747591658447)
  ·
    refine ⟨214654397923087121387487671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143102931948724747591658447 214654397923087121387487671)
    ·
      refine ⟨321981596884630682081231507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214654397923087121387487671 321981596884630682081231507)
      ·
        refine ⟨482972395326946023121847261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321981596884630682081231507 482972395326946023121847261)
        ·
          refine ⟨181114648247604758670692723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482972395326946023121847261 181114648247604758670692723)
          ·
            refine ⟨271671972371407138006039085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181114648247604758670692723 271671972371407138006039085)
            ·
              refine ⟨101876989639277676752264657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271671972371407138006039085 101876989639277676752264657)
              ·
                refine ⟨76407742229458257564198493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101876989639277676752264657 76407742229458257564198493)
                ·
                  refine ⟨28652903336046846586574435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76407742229458257564198493 28652903336046846586574435)
                  ·
                    refine ⟨42979355004070269879861653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28652903336046846586574435 42979355004070269879861653)
                    ·
                      refine ⟨2014657265815793900618515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42979355004070269879861653 2014657265815793900618515)
                      ·
                        rfl

theorem cell23_3923531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_3923531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923531 prefixEnd_3923531 := by exact prefixLift 3923531
  have htrace : WordTrace (prefixWord ++ tailWord_3923531) baseStart_3923531 baseEnd_3923531 := by
    simpa [prefixWord, tailWord_3923531, baseEnd_3923531] using wordTrace_append hprefix tailTrace_3923531
  have hstable : (prefixWord ++ tailWord_3923531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923531).length < 2 ^ (prefixWord ++ tailWord_3923531).sum := by decide
  have hdescent : baseEnd_3923531 < baseStart_3923531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923532 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 1, 5]
def baseStart_3923532 : Nat := 118140960795 + 3923532 * 2 ^ 59
def prefixEnd_3923532 : Nat := 4983230072969 + 3 ^ 40 * 3923532 * 2
def baseEnd_3923532 : Nat := 671552593098816132235337

theorem tailTrace_3923532 : CollatzResearch.WordTrace tailWord_3923532 prefixEnd_3923532 671552593098816132235337 := by
  unfold tailWord_3923532
  simp only [CollatzResearch.WordTrace]
  refine ⟨71551484210860562381222425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95401978947814083174963233 71551484210860562381222425)
  ·
    refine ⟨53663613158145421785916819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71551484210860562381222425 53663613158145421785916819)
    ·
      refine ⟨80495419737218132678875229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53663613158145421785916819 80495419737218132678875229)
      ·
        refine ⟨30185782401456799754578211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80495419737218132678875229 30185782401456799754578211)
        ·
          refine ⟨45278673602185199631867317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30185782401456799754578211 45278673602185199631867317)
          ·
            refine ⟨4244875650204862465487561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45278673602185199631867317 4244875650204862465487561)
            ·
              refine ⟨3183656737653646849115671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4244875650204862465487561 3183656737653646849115671)
              ·
                refine ⟨4775485106480470273673507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183656737653646849115671 4775485106480470273673507)
                ·
                  refine ⟨7163227659720705410510261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775485106480470273673507 7163227659720705410510261)
                  ·
                    refine ⟨671552593098816132235337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7163227659720705410510261 671552593098816132235337)
                    ·
                      rfl

theorem cell23_3923532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_3923532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923532 prefixEnd_3923532 := by exact prefixLift 3923532
  have htrace : WordTrace (prefixWord ++ tailWord_3923532) baseStart_3923532 baseEnd_3923532 := by
    simpa [prefixWord, tailWord_3923532, baseEnd_3923532] using wordTrace_append hprefix tailTrace_3923532
  have hstable : (prefixWord ++ tailWord_3923532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923532).length < 2 ^ (prefixWord ++ tailWord_3923532).sum := by decide
  have hdescent : baseEnd_3923532 < baseStart_3923532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923535 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 7, 2, 2]
def baseStart_3923535 : Nat := 118140960795 + 3923535 * 2 ^ 59
def prefixEnd_3923535 : Nat := 4983230072969 + 3 ^ 40 * 3923535 * 2
def baseEnd_3923535 : Nat := 2014659319738411884968497

theorem tailTrace_3923535 : CollatzResearch.WordTrace tailWord_3923535 prefixEnd_3923535 2014659319738411884968497 := by
  unfold tailWord_3923535
  simp only [CollatzResearch.WordTrace]
  refine ⟨143103077840710256274804059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95402051893806837516536039 143103077840710256274804059)
  ·
    refine ⟨214654616761065384412206089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143103077840710256274804059 214654616761065384412206089)
    ·
      refine ⟨160990962570799038309154567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214654616761065384412206089 160990962570799038309154567)
      ·
        refine ⟨241486443856198557463731851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160990962570799038309154567 241486443856198557463731851)
        ·
          refine ⟨362229665784297836195597777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241486443856198557463731851 362229665784297836195597777)
          ·
            refine ⟨271672249338223377146698333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362229665784297836195597777 271672249338223377146698333)
            ·
              refine ⟨101877093501833766430011875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271672249338223377146698333 101877093501833766430011875)
              ·
                refine ⟨152815640252750649645017813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101877093501833766430011875 152815640252750649645017813)
                ·
                  refine ⟨3581616568423843351055105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 152815640252750649645017813 3581616568423843351055105)
                  ·
                    refine ⟨2686212426317882513291329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581616568423843351055105 2686212426317882513291329)
                    ·
                      refine ⟨2014659319738411884968497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686212426317882513291329 2014659319738411884968497)
                      ·
                        rfl

theorem cell23_3923535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7, 2, 2].length) (baseStart_3923535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923535 prefixEnd_3923535 := by exact prefixLift 3923535
  have htrace : WordTrace (prefixWord ++ tailWord_3923535) baseStart_3923535 baseEnd_3923535 := by
    simpa [prefixWord, tailWord_3923535, baseEnd_3923535] using wordTrace_append hprefix tailTrace_3923535
  have hstable : (prefixWord ++ tailWord_3923535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923535).length < 2 ^ (prefixWord ++ tailWord_3923535).sum := by decide
  have hdescent : baseEnd_3923535 < baseStart_3923535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923551 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_3923551 : Nat := 118140960795 + 3923551 * 2 ^ 59
def prefixEnd_3923551 : Nat := 4983230072969 + 3 ^ 40 * 3923551 * 2
def baseEnd_3923551 : Nat := 2014667535428883822368423

theorem tailTrace_3923551 : CollatzResearch.WordTrace tailWord_3923551 prefixEnd_3923551 2014667535428883822368423 := by
  unfold tailWord_3923551
  simp only [CollatzResearch.WordTrace]
  refine ⟨143103661408652291007386507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95402440939101527338257671 143103661408652291007386507)
  ·
    refine ⟨214655492112978436511079761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143103661408652291007386507 214655492112978436511079761)
    ·
      refine ⟨160991619084733827383309821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214655492112978436511079761 160991619084733827383309821)
      ·
        refine ⟨60371857156775185268741183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160991619084733827383309821 60371857156775185268741183)
        ·
          refine ⟨90557785735162777903111775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60371857156775185268741183 90557785735162777903111775)
          ·
            refine ⟨135836678602744166854667663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90557785735162777903111775 135836678602744166854667663)
            ·
              refine ⟨203755017904116250282001495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135836678602744166854667663 203755017904116250282001495)
              ·
                refine ⟨305632526856174375423002243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203755017904116250282001495 305632526856174375423002243)
                ·
                  refine ⟨458448790284261563134503365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305632526856174375423002243 458448790284261563134503365)
                  ·
                    refine ⟨85959148178299043087719381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 458448790284261563134503365 85959148178299043087719381)
                    ·
                      refine ⟨2014667535428883822368423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85959148178299043087719381 2014667535428883822368423)
                      ·
                        rfl

theorem cell23_3923551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_3923551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923551 prefixEnd_3923551 := by exact prefixLift 3923551
  have htrace : WordTrace (prefixWord ++ tailWord_3923551) baseStart_3923551 baseEnd_3923551 := by
    simpa [prefixWord, tailWord_3923551, baseEnd_3923551] using wordTrace_append hprefix tailTrace_3923551
  have hstable : (prefixWord ++ tailWord_3923551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923551).length < 2 ^ (prefixWord ++ tailWord_3923551).sum := by decide
  have hdescent : baseEnd_3923551 < baseStart_3923551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923565 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_3923565 : Nat := 118140960795 + 3923565 * 2 ^ 59
def prefixEnd_3923565 : Nat := 4983230072969 + 3 ^ 40 * 3923565 * 2
def baseEnd_3923565 : Nat := 2014674724158046767593359

theorem tailTrace_3923565 : CollatzResearch.WordTrace tailWord_3923565 prefixEnd_3923565 2014674724158046767593359 := by
  unfold tailWord_3923565
  simp only [CollatzResearch.WordTrace]
  refine ⟨143104172030601571398396149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95402781353734380932264099 143104172030601571398396149)
  ·
    refine ⟨13416016127868897318599639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143104172030601571398396149 13416016127868897318599639)
    ·
      refine ⟨20124024191803345977899459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13416016127868897318599639 20124024191803345977899459)
      ·
        refine ⟨30186036287705018966849189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20124024191803345977899459 30186036287705018966849189)
        ·
          refine ⟨5659881803944691056284223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30186036287705018966849189 5659881803944691056284223)
          ·
            refine ⟨8489822705917036584426335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5659881803944691056284223 8489822705917036584426335)
            ·
              refine ⟨12734734058875554876639503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8489822705917036584426335 12734734058875554876639503)
              ·
                refine ⟨19102101088313332314959255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12734734058875554876639503 19102101088313332314959255)
                ·
                  refine ⟨28653151632469998472438883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19102101088313332314959255 28653151632469998472438883)
                  ·
                    refine ⟨42979727448704997708658325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28653151632469998472438883 42979727448704997708658325)
                    ·
                      refine ⟨2014674724158046767593359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42979727448704997708658325 2014674724158046767593359)
                      ·
                        rfl

theorem cell23_3923565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_3923565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923565 prefixEnd_3923565 := by exact prefixLift 3923565
  have htrace : WordTrace (prefixWord ++ tailWord_3923565) baseStart_3923565 baseEnd_3923565 := by
    simpa [prefixWord, tailWord_3923565, baseEnd_3923565] using wordTrace_append hprefix tailTrace_3923565
  have hstable : (prefixWord ++ tailWord_3923565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923565).length < 2 ^ (prefixWord ++ tailWord_3923565).sum := by decide
  have hdescent : baseEnd_3923565 < baseStart_3923565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923571 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 9]
def baseStart_3923571 : Nat := 118140960795 + 3923571 * 2 ^ 59
def prefixEnd_3923571 : Nat := 4983230072969 + 3 ^ 40 * 3923571 * 2
def baseEnd_3923571 : Nat := 671559268347324581372777

theorem tailTrace_3923571 : CollatzResearch.WordTrace tailWord_3923571 prefixEnd_3923571 671559268347324581372777 := by
  unfold tailWord_3923571
  simp only [CollatzResearch.WordTrace]
  refine ⟨143104390868579834423114567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95402927245719889615409711 143104390868579834423114567)
  ·
    refine ⟨214656586302869751634671851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143104390868579834423114567 214656586302869751634671851)
    ·
      refine ⟨321984879454304627452007777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214656586302869751634671851 321984879454304627452007777)
      ·
        refine ⟨241488659590728470589005833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321984879454304627452007777 241488659590728470589005833)
        ·
          refine ⟨181116494693046352941754375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241488659590728470589005833 181116494693046352941754375)
          ·
            refine ⟨271674742039569529412631563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181116494693046352941754375 271674742039569529412631563)
            ·
              refine ⟨407512113059354294118947345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271674742039569529412631563 407512113059354294118947345)
              ·
                refine ⟨305634084794515720589210509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407512113059354294118947345 305634084794515720589210509)
                ·
                  refine ⟨114612781797943395220953941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305634084794515720589210509 114612781797943395220953941)
                  ·
                    refine ⟨671559268347324581372777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 114612781797943395220953941 671559268347324581372777)
                    ·
                      rfl

theorem cell23_3923571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 9].length) (baseStart_3923571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923571 prefixEnd_3923571 := by exact prefixLift 3923571
  have htrace : WordTrace (prefixWord ++ tailWord_3923571) baseStart_3923571 baseEnd_3923571 := by
    simpa [prefixWord, tailWord_3923571, baseEnd_3923571] using wordTrace_append hprefix tailTrace_3923571
  have hstable : (prefixWord ++ tailWord_3923571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923571).length < 2 ^ (prefixWord ++ tailWord_3923571).sum := by decide
  have hdescent : baseEnd_3923571 < baseStart_3923571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923592 : List Nat := [2, 1, 3, 5, 2, 1, 9]
def baseStart_3923592 : Nat := 118140960795 + 3923592 * 2 ^ 59
def prefixEnd_3923592 : Nat := 4983230072969 + 3 ^ 40 * 3923592 * 2
def baseEnd_3923592 : Nat := 24872698618959483480935

theorem tailTrace_3923592 : CollatzResearch.WordTrace tailWord_3923592 prefixEnd_3923592 24872698618959483480935 := by
  unfold tailWord_3923592
  simp only [CollatzResearch.WordTrace]
  refine ⟨71552578400751877504814515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95403437867669170006419353 71552578400751877504814515)
  ·
    refine ⟨107328867601127816257221773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71552578400751877504814515 107328867601127816257221773)
    ·
      refine ⟨40248325350422931096458165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107328867601127816257221773 40248325350422931096458165)
      ·
        refine ⟨3773280501602149790292953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40248325350422931096458165 3773280501602149790292953)
        ·
          refine ⟨2829960376201612342719715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3773280501602149790292953 2829960376201612342719715)
          ·
            refine ⟨4244940564302418514079573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829960376201612342719715 4244940564302418514079573)
            ·
              refine ⟨24872698618959483480935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4244940564302418514079573 24872698618959483480935)
              ·
                rfl

theorem cell23_3923592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 9].length) (baseStart_3923592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923592 prefixEnd_3923592 := by exact prefixLift 3923592
  have htrace : WordTrace (prefixWord ++ tailWord_3923592) baseStart_3923592 baseEnd_3923592 := by
    simpa [prefixWord, tailWord_3923592, baseEnd_3923592] using wordTrace_append hprefix tailTrace_3923592
  have hstable : (prefixWord ++ tailWord_3923592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923592).length < 2 ^ (prefixWord ++ tailWord_3923592).sum := by decide
  have hdescent : baseEnd_3923592 < baseStart_3923592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923642 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2]
def baseStart_3923642 : Nat := 118140960795 + 3923642 * 2 ^ 59
def prefixEnd_3923642 : Nat := 4983230072969 + 3 ^ 40 * 3923642 * 2
def baseEnd_3923642 : Nat := 2014714262168442966330505

theorem tailTrace_3923642 : CollatzResearch.WordTrace tailWord_3923642 prefixEnd_3923642 2014714262168442966330505 := by
  unfold tailWord_3923642
  simp only [CollatzResearch.WordTrace]
  refine ⟨35776745112830653387237295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95404653634215075699299453 35776745112830653387237295)
  ·
    refine ⟨53665117669245980080855943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35776745112830653387237295 53665117669245980080855943)
    ·
      refine ⟨80497676503868970121283915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53665117669245980080855943 80497676503868970121283915)
      ·
        refine ⟨120746514755803455181925873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80497676503868970121283915 120746514755803455181925873)
        ·
          refine ⟨90559886066852591386444405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120746514755803455181925873 90559886066852591386444405)
          ·
            refine ⟨8489989318767430442479163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90559886066852591386444405 8489989318767430442479163)
            ·
              refine ⟨12734983978151145663718745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8489989318767430442479163 12734983978151145663718745)
              ·
                refine ⟨9551237983613359247789059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12734983978151145663718745 9551237983613359247789059)
                ·
                  refine ⟨14326856975420038871683589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9551237983613359247789059 14326856975420038871683589)
                  ·
                    refine ⟨2686285682891257288440673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14326856975420038871683589 2686285682891257288440673)
                    ·
                      refine ⟨2014714262168442966330505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686285682891257288440673 2014714262168442966330505)
                      ·
                        rfl

theorem cell23_3923642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_3923642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923642 prefixEnd_3923642 := by exact prefixLift 3923642
  have htrace : WordTrace (prefixWord ++ tailWord_3923642) baseStart_3923642 baseEnd_3923642 := by
    simpa [prefixWord, tailWord_3923642, baseEnd_3923642] using wordTrace_append hprefix tailTrace_3923642
  have hstable : (prefixWord ++ tailWord_3923642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923642).length < 2 ^ (prefixWord ++ tailWord_3923642).sum := by decide
  have hdescent : baseEnd_3923642 < baseStart_3923642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923646 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_3923646 : Nat := 118140960795 + 3923646 * 2 ^ 59
def prefixEnd_3923646 : Nat := 4983230072969 + 3 ^ 40 * 3923646 * 2
def baseEnd_3923646 : Nat := 2014716316091060950680487

theorem tailTrace_3923646 : CollatzResearch.WordTrace tailWord_3923646 prefixEnd_3923646 2014716316091060950680487 := by
  unfold tailWord_3923646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17888390792913515279011849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95404750895538748154729861 17888390792913515279011849)
  ·
    refine ⟨13416293094685136459258887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17888390792913515279011849 13416293094685136459258887)
    ·
      refine ⟨20124439642027704688888331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13416293094685136459258887 20124439642027704688888331)
      ·
        refine ⟨30186659463041557033332497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20124439642027704688888331 30186659463041557033332497)
        ·
          refine ⟨22639994597281167774999373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30186659463041557033332497 22639994597281167774999373)
          ·
            refine ⟨8489997973980437915624765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22639994597281167774999373 8489997973980437915624765)
            ·
              refine ⟨3183749240242664218359287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8489997973980437915624765 3183749240242664218359287)
              ·
                refine ⟨4775623860363996327538931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183749240242664218359287 4775623860363996327538931)
                ·
                  refine ⟨7163435790545994491308397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775623860363996327538931 7163435790545994491308397)
                  ·
                    refine ⟨2686288421454747934240649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7163435790545994491308397 2686288421454747934240649)
                    ·
                      refine ⟨2014716316091060950680487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686288421454747934240649 2014716316091060950680487)
                      ·
                        rfl

theorem cell23_3923646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_3923646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923646 prefixEnd_3923646 := by exact prefixLift 3923646
  have htrace : WordTrace (prefixWord ++ tailWord_3923646) baseStart_3923646 baseEnd_3923646 := by
    simpa [prefixWord, tailWord_3923646, baseEnd_3923646] using wordTrace_append hprefix tailTrace_3923646
  have hstable : (prefixWord ++ tailWord_3923646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923646).length < 2 ^ (prefixWord ++ tailWord_3923646).sum := by decide
  have hdescent : baseEnd_3923646 < baseStart_3923646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923676 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 1, 4, 2]
def baseStart_3923676 : Nat := 118140960795 + 3923676 * 2 ^ 59
def prefixEnd_3923676 : Nat := 4983230072969 + 3 ^ 40 * 3923676 * 2
def baseEnd_3923676 : Nat := 2014731720510695833305349

theorem tailTrace_3923676 : CollatzResearch.WordTrace tailWord_3923676 prefixEnd_3923676 2014731720510695833305349 := by
  unfold tailWord_3923676
  simp only [CollatzResearch.WordTrace]
  refine ⟨71554110266599718677843441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95405480355466291570457921 71554110266599718677843441)
  ·
    refine ⟨53665582699949789008382581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71554110266599718677843441 53665582699949789008382581)
    ·
      refine ⟨5031148378120292719535867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53665582699949789008382581 5031148378120292719535867)
      ·
        refine ⟨7546722567180439079303801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5031148378120292719535867 7546722567180439079303801)
        ·
          refine ⟨5660041925385329309477851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7546722567180439079303801 5660041925385329309477851)
          ·
            refine ⟨8490062888077993964216777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660041925385329309477851 8490062888077993964216777)
            ·
              refine ⟨6367547166058495473162583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8490062888077993964216777 6367547166058495473162583)
              ·
                refine ⟨9551320749087743209743875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367547166058495473162583 9551320749087743209743875)
                ·
                  refine ⟨14326981123631614814615813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9551320749087743209743875 14326981123631614814615813)
                  ·
                    refine ⟨2686308960680927777740465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14326981123631614814615813 2686308960680927777740465)
                    ·
                      refine ⟨2014731720510695833305349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686308960680927777740465 2014731720510695833305349)
                      ·
                        rfl

theorem cell23_3923676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_3923676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923676 prefixEnd_3923676 := by exact prefixLift 3923676
  have htrace : WordTrace (prefixWord ++ tailWord_3923676) baseStart_3923676 baseEnd_3923676 := by
    simpa [prefixWord, tailWord_3923676, baseEnd_3923676] using wordTrace_append hprefix tailTrace_3923676
  have hstable : (prefixWord ++ tailWord_3923676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923676).length < 2 ^ (prefixWord ++ tailWord_3923676).sum := by decide
  have hdescent : baseEnd_3923676 < baseStart_3923676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923710 : List Nat := [4, 2, 2, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3923710 : Nat := 118140960795 + 3923710 * 2 ^ 59
def prefixEnd_3923710 : Nat := 4983230072969 + 3 ^ 40 * 3923710 * 2
def baseEnd_3923710 : Nat := 2014749178852948700280193

theorem tailTrace_3923710 : CollatzResearch.WordTrace tailWord_3923710 prefixEnd_3923710 2014749178852948700280193 := by
  unfold tailWord_3923710
  simp only [CollatzResearch.WordTrace]
  refine ⟨17888682576884532645303073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95406307076717507441616389 17888682576884532645303073)
  ·
    refine ⟨13416511932663399483977305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17888682576884532645303073 13416511932663399483977305)
    ·
      refine ⟨10062383949497549612982979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13416511932663399483977305 10062383949497549612982979)
      ·
        refine ⟨15093575924246324419474469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10062383949497549612982979 15093575924246324419474469)
        ·
          refine ⟨2830045485796185828651463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15093575924246324419474469 2830045485796185828651463)
          ·
            refine ⟨4245068228694278742977195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830045485796185828651463 4245068228694278742977195)
            ·
              refine ⟨6367602343041418114465793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245068228694278742977195 6367602343041418114465793)
              ·
                refine ⟨4775701757281063585849345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6367602343041418114465793 4775701757281063585849345)
                ·
                  refine ⟨3581776317960797689387009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4775701757281063585849345 3581776317960797689387009)
                  ·
                    refine ⟨2686332238470598267040257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581776317960797689387009 2686332238470598267040257)
                    ·
                      refine ⟨2014749178852948700280193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686332238470598267040257 2014749178852948700280193)
                      ·
                        rfl

theorem cell23_3923710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3923710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923710 prefixEnd_3923710 := by exact prefixLift 3923710
  have htrace : WordTrace (prefixWord ++ tailWord_3923710) baseStart_3923710 baseEnd_3923710 := by
    simpa [prefixWord, tailWord_3923710, baseEnd_3923710] using wordTrace_append hprefix tailTrace_3923710
  have hstable : (prefixWord ++ tailWord_3923710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923710).length < 2 ^ (prefixWord ++ tailWord_3923710).sum := by decide
  have hdescent : baseEnd_3923710 < baseStart_3923710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923715 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 4]
def baseStart_3923715 : Nat := 118140960795 + 3923715 * 2 ^ 59
def prefixEnd_3923715 : Nat := 4983230072969 + 3 ^ 40 * 3923715 * 2
def baseEnd_3923715 : Nat := 2014751746256221180717669

theorem tailTrace_3923715 : CollatzResearch.WordTrace tailWord_3923715 prefixEnd_3923715 2014751746256221180717669 := by
  unfold tailWord_3923715
  simp only [CollatzResearch.WordTrace]
  refine ⟨143109642980058147016356599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95406428653372098010904399 143109642980058147016356599)
  ·
    refine ⟨214664464470087220524534899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143109642980058147016356599 214664464470087220524534899)
    ·
      refine ⟨321996696705130830786802349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214664464470087220524534899 321996696705130830786802349)
      ·
        refine ⟨120748761264424061545050881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321996696705130830786802349 120748761264424061545050881)
        ·
          refine ⟨90561570948318046158788161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120748761264424061545050881 90561570948318046158788161)
          ·
            refine ⟨67921178211238534619091121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90561570948318046158788161 67921178211238534619091121)
            ·
              refine ⟨50940883658428900964318341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67921178211238534619091121 50940883658428900964318341)
              ·
                refine ⟨9551415685955418930809689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50940883658428900964318341 9551415685955418930809689)
                ·
                  refine ⟨7163561764466564198107267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9551415685955418930809689 7163561764466564198107267)
                  ·
                    refine ⟨10745342646699846297160901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7163561764466564198107267 10745342646699846297160901)
                    ·
                      refine ⟨2014751746256221180717669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10745342646699846297160901 2014751746256221180717669)
                      ·
                        rfl

theorem cell23_3923715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_3923715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923715 prefixEnd_3923715 := by exact prefixLift 3923715
  have htrace : WordTrace (prefixWord ++ tailWord_3923715) baseStart_3923715 baseEnd_3923715 := by
    simpa [prefixWord, tailWord_3923715, baseEnd_3923715] using wordTrace_append hprefix tailTrace_3923715
  have hstable : (prefixWord ++ tailWord_3923715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923715).length < 2 ^ (prefixWord ++ tailWord_3923715).sum := by decide
  have hdescent : baseEnd_3923715 < baseStart_3923715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923752 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3923752 : Nat := 118140960795 + 3923752 * 2 ^ 59
def prefixEnd_3923752 : Nat := 4983230072969 + 3 ^ 40 * 3923752 * 2
def baseEnd_3923752 : Nat := 2014770745040437535954999

theorem tailTrace_3923752 : CollatzResearch.WordTrace tailWord_3923752 prefixEnd_3923752 2014770745040437535954999 := by
  unfold tailWord_3923752
  simp only [CollatzResearch.WordTrace]
  refine ⟨71555496240462051167726755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95407328320616068223635673 71555496240462051167726755)
  ·
    refine ⟨107333244360693076751590133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71555496240462051167726755 107333244360693076751590133)
    ·
      refine ⟨10062491658814975945461575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107333244360693076751590133 10062491658814975945461575)
      ·
        refine ⟨15093737488222463918192363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10062491658814975945461575 15093737488222463918192363)
        ·
          refine ⟨22640606232333695877288545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15093737488222463918192363 22640606232333695877288545)
          ·
            refine ⟨16980454674250271907966409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22640606232333695877288545 16980454674250271907966409)
            ·
              refine ⟨12735341005687703930974807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16980454674250271907966409 12735341005687703930974807)
              ·
                refine ⟨19103011508531555896462211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12735341005687703930974807 19103011508531555896462211)
                ·
                  refine ⟨28654517262797333844693317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19103011508531555896462211 28654517262797333844693317)
                  ·
                    refine ⟨5372721986774500095879997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28654517262797333844693317 5372721986774500095879997)
                    ·
                      refine ⟨2014770745040437535954999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5372721986774500095879997 2014770745040437535954999)
                      ·
                        rfl

theorem cell23_3923752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3923752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923752 prefixEnd_3923752 := by exact prefixLift 3923752
  have htrace : WordTrace (prefixWord ++ tailWord_3923752) baseStart_3923752 baseEnd_3923752 := by
    simpa [prefixWord, tailWord_3923752, baseEnd_3923752] using wordTrace_append hprefix tailTrace_3923752
  have hstable : (prefixWord ++ tailWord_3923752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923752).length < 2 ^ (prefixWord ++ tailWord_3923752).sum := by decide
  have hdescent : baseEnd_3923752 < baseStart_3923752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923785 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 3, 5]
def baseStart_3923785 : Nat := 118140960795 + 3923785 * 2 ^ 59
def prefixEnd_3923785 : Nat := 4983230072969 + 3 ^ 40 * 3923785 * 2
def baseEnd_3923785 : Nat := 671595896634011968947449

theorem tailTrace_3923785 : CollatzResearch.WordTrace tailWord_3923785 prefixEnd_3923785 671595896634011968947449 := by
  unfold tailWord_3923785
  simp only [CollatzResearch.WordTrace]
  refine ⟨143112196089804548971404809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95408130726536365980936539 143112196089804548971404809)
  ·
    refine ⟨107334147067353411728553607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143112196089804548971404809 107334147067353411728553607)
    ·
      refine ⟨161001220601030117592830411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107334147067353411728553607 161001220601030117592830411)
      ·
        refine ⟨241501830901545176389245617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161001220601030117592830411 241501830901545176389245617)
        ·
          refine ⟨181126373176158882291934213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241501830901545176389245617 181126373176158882291934213)
          ·
            refine ⟨33961194970529790429737665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181126373176158882291934213 33961194970529790429737665)
            ·
              refine ⟨25470896227897342822303249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33961194970529790429737665 25470896227897342822303249)
              ·
                refine ⟨19103172170923007116727437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25470896227897342822303249 19103172170923007116727437)
                ·
                  refine ⟨7163689564096127668772789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19103172170923007116727437 7163689564096127668772789)
                  ·
                    refine ⟨671595896634011968947449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7163689564096127668772789 671595896634011968947449)
                    ·
                      rfl

theorem cell23_3923785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_3923785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923785 prefixEnd_3923785 := by exact prefixLift 3923785
  have htrace : WordTrace (prefixWord ++ tailWord_3923785) baseStart_3923785 baseEnd_3923785 := by
    simpa [prefixWord, tailWord_3923785, baseEnd_3923785] using wordTrace_append hprefix tailTrace_3923785
  have hstable : (prefixWord ++ tailWord_3923785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923785).length < 2 ^ (prefixWord ++ tailWord_3923785).sum := by decide
  have hdescent : baseEnd_3923785 < baseStart_3923785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923789 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 6]
def baseStart_3923789 : Nat := 118140960795 + 3923789 * 2 ^ 59
def prefixEnd_3923789 : Nat := 4983230072969 + 3 ^ 40 * 3923789 * 2
def baseEnd_3923789 : Nat := 223865527091628210132481

theorem tailTrace_3923789 : CollatzResearch.WordTrace tailWord_3923789 prefixEnd_3923789 223865527091628210132481 := by
  unfold tailWord_3923789
  simp only [CollatzResearch.WordTrace]
  refine ⟨143112341981790057654550421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95408227987860038436366947 143112341981790057654550421)
  ·
    refine ⟨6708391030396408952557051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143112341981790057654550421 6708391030396408952557051)
    ·
      refine ⟨10062586545594613428835577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6708391030396408952557051 10062586545594613428835577)
      ·
        refine ⟨7546939909195960071626683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10062586545594613428835577 7546939909195960071626683)
        ·
          refine ⟨11320409863793940107440025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7546939909195960071626683 11320409863793940107440025)
          ·
            refine ⟨8490307397845455080580019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11320409863793940107440025 8490307397845455080580019)
            ·
              refine ⟨12735461096768182620870029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8490307397845455080580019 12735461096768182620870029)
              ·
                refine ⟨4775797911288068482826261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12735461096768182620870029 4775797911288068482826261)
                ·
                  refine ⟨223865527091628210132481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4775797911288068482826261 223865527091628210132481)
                  ·
                    rfl

theorem cell23_3923789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_3923789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923789 prefixEnd_3923789 := by exact prefixLift 3923789
  have htrace : WordTrace (prefixWord ++ tailWord_3923789) baseStart_3923789 baseEnd_3923789 := by
    simpa [prefixWord, tailWord_3923789, baseEnd_3923789] using wordTrace_append hprefix tailTrace_3923789
  have hstable : (prefixWord ++ tailWord_3923789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923789).length < 2 ^ (prefixWord ++ tailWord_3923789).sum := by decide
  have hdescent : baseEnd_3923789 < baseStart_3923789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923792 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 6, 3, 2]
def baseStart_3923792 : Nat := 118140960795 + 3923792 * 2 ^ 59
def prefixEnd_3923792 : Nat := 4983230072969 + 3 ^ 40 * 3923792 * 2
def baseEnd_3923792 : Nat := 2014791284266617379454815

theorem tailTrace_3923792 : CollatzResearch.WordTrace tailWord_3923792 prefixEnd_3923792 2014791284266617379454815 := by
  unfold tailWord_3923792
  simp only [CollatzResearch.WordTrace]
  refine ⟨71556225700389594583454815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95408300933852792777939753 71556225700389594583454815)
  ·
    refine ⟨107334338550584391875182223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71556225700389594583454815 107334338550584391875182223)
    ·
      refine ⟨161001507825876587812773335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107334338550584391875182223 161001507825876587812773335)
      ·
        refine ⟨241502261738814881719160003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161001507825876587812773335 241502261738814881719160003)
        ·
          refine ⟨362253392608222322578740005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241502261738814881719160003 362253392608222322578740005)
          ·
            refine ⟨67922511114041685483513751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362253392608222322578740005 67922511114041685483513751)
            ·
              refine ⟨101883766671062528225270627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67922511114041685483513751 101883766671062528225270627)
              ·
                refine ⟨152825650006593792337905941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101883766671062528225270627 152825650006593792337905941)
                ·
                  refine ⟨7163702344059084015839341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152825650006593792337905941 7163702344059084015839341)
                  ·
                    refine ⟨2686388379022156505939753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7163702344059084015839341 2686388379022156505939753)
                    ·
                      refine ⟨2014791284266617379454815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686388379022156505939753 2014791284266617379454815)
                      ·
                        rfl

theorem cell23_3923792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 6, 3, 2].length) (baseStart_3923792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923792 prefixEnd_3923792 := by exact prefixLift 3923792
  have htrace : WordTrace (prefixWord ++ tailWord_3923792) baseStart_3923792 baseEnd_3923792 := by
    simpa [prefixWord, tailWord_3923792, baseEnd_3923792] using wordTrace_append hprefix tailTrace_3923792
  have hstable : (prefixWord ++ tailWord_3923792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923792).length < 2 ^ (prefixWord ++ tailWord_3923792).sum := by decide
  have hdescent : baseEnd_3923792 < baseStart_3923792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923809 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_3923809 : Nat := 118140960795 + 3923809 * 2 ^ 59
def prefixEnd_3923809 : Nat := 4983230072969 + 3 ^ 40 * 3923809 * 2
def baseEnd_3923809 : Nat := 2014800013437743812942237

theorem tailTrace_3923809 : CollatzResearch.WordTrace tailWord_3923809 prefixEnd_3923809 2014800013437743812942237 := by
  unfold tailWord_3923809
  simp only [CollatzResearch.WordTrace]
  refine ⟨143113071441717601070278481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95408714294478400713518987 143113071441717601070278481)
  ·
    refine ⟨107334803581288200802708861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143113071441717601070278481 107334803581288200802708861)
    ·
      refine ⟨40250551342983075301015823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107334803581288200802708861 40250551342983075301015823)
      ·
        refine ⟨60375827014474612951523735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40250551342983075301015823 60375827014474612951523735)
        ·
          refine ⟨90563740521711919427285603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60375827014474612951523735 90563740521711919427285603)
          ·
            refine ⟨135845610782567879140928405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90563740521711919427285603 135845610782567879140928405)
            ·
              refine ⟨6367763005432869334731019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135845610782567879140928405 6367763005432869334731019)
              ·
                refine ⟨9551644508149304002096529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367763005432869334731019 9551644508149304002096529)
                ·
                  refine ⟨7163733381111978001572397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9551644508149304002096529 7163733381111978001572397)
                  ·
                    refine ⟨2686400017916991750589649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7163733381111978001572397 2686400017916991750589649)
                    ·
                      refine ⟨2014800013437743812942237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686400017916991750589649 2014800013437743812942237)
                      ·
                        rfl

theorem cell23_3923809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_3923809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923809 prefixEnd_3923809 := by exact prefixLift 3923809
  have htrace : WordTrace (prefixWord ++ tailWord_3923809) baseStart_3923809 baseEnd_3923809 := by
    simpa [prefixWord, tailWord_3923809, baseEnd_3923809] using wordTrace_append hprefix tailTrace_3923809
  have hstable : (prefixWord ++ tailWord_3923809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923809).length < 2 ^ (prefixWord ++ tailWord_3923809).sum := by decide
  have hdescent : baseEnd_3923809 < baseStart_3923809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923816 : List Nat := [2, 1, 4, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3923816 : Nat := 118140960795 + 3923816 * 2 ^ 59
def prefixEnd_3923816 : Nat := 4983230072969 + 3 ^ 40 * 3923816 * 2
def baseEnd_3923816 : Nat := 2014803607802325285554705

theorem tailTrace_3923816 : CollatzResearch.WordTrace tailWord_3923816 prefixEnd_3923816 2014803607802325285554705 := by
  unfold tailWord_3923816
  simp only [CollatzResearch.WordTrace]
  refine ⟨71556663376346120632891651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95408884501794827510522201 71556663376346120632891651)
  ·
    refine ⟨107334995064519180949337477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71556663376346120632891651 107334995064519180949337477)
    ·
      refine ⟨20125311574597346428000777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107334995064519180949337477 20125311574597346428000777)
      ·
        refine ⟨15093983680948009821000583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20125311574597346428000777 15093983680948009821000583)
        ·
          refine ⟨22640975521422014731500875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15093983680948009821000583 22640975521422014731500875)
          ·
            refine ⟨33961463282133022097251313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22640975521422014731500875 33961463282133022097251313)
            ·
              refine ⟨25471097461599766572938485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33961463282133022097251313 25471097461599766572938485)
              ·
                refine ⟨2387915387024978116212983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25471097461599766572938485 2387915387024978116212983)
                ·
                  refine ⟨3581873080537467174319475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387915387024978116212983 3581873080537467174319475)
                  ·
                    refine ⟨5372809620806200761479213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3581873080537467174319475 5372809620806200761479213)
                    ·
                      refine ⟨2014803607802325285554705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5372809620806200761479213 2014803607802325285554705)
                      ·
                        rfl

theorem cell23_3923816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3923816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923816 prefixEnd_3923816 := by exact prefixLift 3923816
  have htrace : WordTrace (prefixWord ++ tailWord_3923816) baseStart_3923816 baseEnd_3923816 := by
    simpa [prefixWord, tailWord_3923816, baseEnd_3923816] using wordTrace_append hprefix tailTrace_3923816
  have hstable : (prefixWord ++ tailWord_3923816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923816).length < 2 ^ (prefixWord ++ tailWord_3923816).sum := by decide
  have hdescent : baseEnd_3923816 < baseStart_3923816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923835 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4]
def baseStart_3923835 : Nat := 118140960795 + 3923835 * 2 ^ 59
def prefixEnd_3923835 : Nat := 4983230072969 + 3 ^ 40 * 3923835 * 2
def baseEnd_3923835 : Nat := 2014813363934760711217117

theorem tailTrace_3923835 : CollatzResearch.WordTrace tailWord_3923835 prefixEnd_3923835 2014813363934760711217117 := by
  unfold tailWord_3923835
  simp only [CollatzResearch.WordTrace]
  refine ⟨143114019739623407510724959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95409346493082271673816639 143114019739623407510724959)
  ·
    refine ⟨214671029609435111266087439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143114019739623407510724959 214671029609435111266087439)
    ·
      refine ⟨322006544414152666899131159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214671029609435111266087439 322006544414152666899131159)
      ·
        refine ⟨483009816621229000348696739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322006544414152666899131159 483009816621229000348696739)
        ·
          refine ⟨724514724931843500523045109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483009816621229000348696739 724514724931843500523045109)
          ·
            refine ⟨67923255462360328174035479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 724514724931843500523045109 67923255462360328174035479)
            ·
              refine ⟨101884883193540492261053219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67923255462360328174035479 101884883193540492261053219)
              ·
                refine ⟨152827324790310738391579829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101884883193540492261053219 152827324790310738391579829)
                ·
                  refine ⟨14327561699091631724210609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152827324790310738391579829 14327561699091631724210609)
                  ·
                    refine ⟨10745671274318723793157957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14327561699091631724210609 10745671274318723793157957)
                    ·
                      refine ⟨2014813363934760711217117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10745671274318723793157957 2014813363934760711217117)
                      ·
                        rfl

theorem cell23_3923835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_3923835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923835 prefixEnd_3923835 := by exact prefixLift 3923835
  have htrace : WordTrace (prefixWord ++ tailWord_3923835) baseStart_3923835 baseEnd_3923835 := by
    simpa [prefixWord, tailWord_3923835, baseEnd_3923835] using wordTrace_append hprefix tailTrace_3923835
  have hstable : (prefixWord ++ tailWord_3923835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923835).length < 2 ^ (prefixWord ++ tailWord_3923835).sum := by decide
  have hdescent : baseEnd_3923835 < baseStart_3923835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923839 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 3, 2, 2]
def baseStart_3923839 : Nat := 118140960795 + 3923839 * 2 ^ 59
def prefixEnd_3923839 : Nat := 4983230072969 + 3 ^ 40 * 3923839 * 2
def baseEnd_3923839 : Nat := 2014815417857378695567099

theorem tailTrace_3923839 : CollatzResearch.WordTrace tailWord_3923839 prefixEnd_3923839 2014815417857378695567099 := by
  unfold tailWord_3923839
  simp only [CollatzResearch.WordTrace]
  refine ⟨143114165631608916193870571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95409443754405944129247047 143114165631608916193870571)
  ·
    refine ⟨214671248447413374290805857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143114165631608916193870571 214671248447413374290805857)
    ·
      refine ⟨161003436335560030718104393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214671248447413374290805857 161003436335560030718104393)
      ·
        refine ⟨120752577251670023038578295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161003436335560030718104393 120752577251670023038578295)
        ·
          refine ⟨181128865877505034557867443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120752577251670023038578295 181128865877505034557867443)
          ·
            refine ⟨271693298816257551836801165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181128865877505034557867443 271693298816257551836801165)
            ·
              refine ⟨101884987056096581938800437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271693298816257551836801165 101884987056096581938800437)
              ·
                refine ⟨9551717536509054556762541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101884987056096581938800437 9551717536509054556762541)
                ·
                  refine ⟨3581894076190895458785953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9551717536509054556762541 3581894076190895458785953)
                  ·
                    refine ⟨2686420557143171594089465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581894076190895458785953 2686420557143171594089465)
                    ·
                      refine ⟨2014815417857378695567099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686420557143171594089465 2014815417857378695567099)
                      ·
                        rfl

theorem cell23_3923839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 3, 2, 2].length) (baseStart_3923839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923839 prefixEnd_3923839 := by exact prefixLift 3923839
  have htrace : WordTrace (prefixWord ++ tailWord_3923839) baseStart_3923839 baseEnd_3923839 := by
    simpa [prefixWord, tailWord_3923839, baseEnd_3923839] using wordTrace_append hprefix tailTrace_3923839
  have hstable : (prefixWord ++ tailWord_3923839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923839).length < 2 ^ (prefixWord ++ tailWord_3923839).sum := by decide
  have hdescent : baseEnd_3923839 < baseStart_3923839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923870 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_3923870 : Nat := 118140960795 + 3923870 * 2 ^ 59
def prefixEnd_3923870 : Nat := 4983230072969 + 3 ^ 40 * 3923870 * 2
def baseEnd_3923870 : Nat := 671610445252556024759819

theorem tailTrace_3923870 : CollatzResearch.WordTrace tailWord_3923870 prefixEnd_3923870 671610445252556024759819 := by
  unfold tailWord_3923870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17889412036812076061031133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95410197529664405658832709 17889412036812076061031133)
  ·
    refine ⟨6708529513804528522886675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17889412036812076061031133 6708529513804528522886675)
    ·
      refine ⟨10062794270706792784330013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6708529513804528522886675 10062794270706792784330013)
      ·
        refine ⟨3773547851515047294123755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10062794270706792784330013 3773547851515047294123755)
        ·
          refine ⟨5660321777272570941185633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3773547851515047294123755 5660321777272570941185633)
          ·
            refine ⟨4245241332954428205889225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5660321777272570941185633 4245241332954428205889225)
            ·
              refine ⟨3183930999715821154416919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245241332954428205889225 3183930999715821154416919)
              ·
                refine ⟨4775896499573731731625379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183930999715821154416919 4775896499573731731625379)
                ·
                  refine ⟨7163844749360597597438069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775896499573731731625379 7163844749360597597438069)
                  ·
                    refine ⟨671610445252556024759819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7163844749360597597438069 671610445252556024759819)
                    ·
                      rfl

theorem cell23_3923870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_3923870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923870 prefixEnd_3923870 := by exact prefixLift 3923870
  have htrace : WordTrace (prefixWord ++ tailWord_3923870) baseStart_3923870 baseEnd_3923870 := by
    simpa [prefixWord, tailWord_3923870, baseEnd_3923870] using wordTrace_append hprefix tailTrace_3923870
  have hstable : (prefixWord ++ tailWord_3923870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923870).length < 2 ^ (prefixWord ++ tailWord_3923870).sum := by decide
  have hdescent : baseEnd_3923870 < baseStart_3923870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923873 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_3923873 : Nat := 118140960795 + 3923873 * 2 ^ 59
def prefixEnd_3923873 : Nat := 4983230072969 + 3 ^ 40 * 3923873 * 2
def baseEnd_3923873 : Nat := 2014832876199631562541943

theorem tailTrace_3923873 : CollatzResearch.WordTrace tailWord_3923873 prefixEnd_3923873 2014832876199631562541943 := by
  unfold tailWord_3923873
  simp only [CollatzResearch.WordTrace]
  refine ⟨143115405713485740000608273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95410270475657160000405515 143115405713485740000608273)
  ·
    refine ⟨107336554285114305000456205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143115405713485740000608273 107336554285114305000456205)
    ·
      refine ⟨40251207856917864375171077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107336554285114305000456205 40251207856917864375171077)
      ·
        refine ⟨7547101473172099570344577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40251207856917864375171077 7547101473172099570344577)
        ·
          refine ⟨5660326104879074677758433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7547101473172099570344577 5660326104879074677758433)
          ·
            refine ⟨4245244578659306008318825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5660326104879074677758433 4245244578659306008318825)
            ·
              refine ⟨3183933433994479506239119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4245244578659306008318825 3183933433994479506239119)
              ·
                refine ⟨4775900150991719259358679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183933433994479506239119 4775900150991719259358679)
                ·
                  refine ⟨7163850226487578889038019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775900150991719259358679 7163850226487578889038019)
                  ·
                    refine ⟨10745775339731368333557029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7163850226487578889038019 10745775339731368333557029)
                    ·
                      refine ⟨2014832876199631562541943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10745775339731368333557029 2014832876199631562541943)
                      ·
                        rfl

theorem cell23_3923873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_3923873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923873 prefixEnd_3923873 := by exact prefixLift 3923873
  have htrace : WordTrace (prefixWord ++ tailWord_3923873) baseStart_3923873 baseEnd_3923873 := by
    simpa [prefixWord, tailWord_3923873, baseEnd_3923873] using wordTrace_append hprefix tailTrace_3923873
  have hstable : (prefixWord ++ tailWord_3923873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923873).length < 2 ^ (prefixWord ++ tailWord_3923873).sum := by decide
  have hdescent : baseEnd_3923873 < baseStart_3923873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923876 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_3923876 : Nat := 118140960795 + 3923876 * 2 ^ 59
def prefixEnd_3923876 : Nat := 4983230072969 + 3 ^ 40 * 3923876 * 2
def baseEnd_3923876 : Nat := 2014834416641595050804429

theorem tailTrace_3923876 : CollatzResearch.WordTrace tailWord_3923876 prefixEnd_3923876 2014834416641595050804429 := by
  unfold tailWord_3923876
  simp only [CollatzResearch.WordTrace]
  refine ⟨71557757566237435756483741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95410343421649914341978321 71557757566237435756483741)
  ·
    refine ⟨26834159087339038408681403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71557757566237435756483741 26834159087339038408681403)
    ·
      refine ⟨40251238631008557613022105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26834159087339038408681403 40251238631008557613022105)
      ·
        refine ⟨30188428973256418209766579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40251238631008557613022105 30188428973256418209766579)
        ·
          refine ⟨45282643459884627314649869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30188428973256418209766579 45282643459884627314649869)
          ·
            refine ⟨16980991297456735242993701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45282643459884627314649869 16980991297456735242993701)
            ·
              refine ⟨3183935868273137858061319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16980991297456735242993701 3183935868273137858061319)
              ·
                refine ⟨4775903802409706787091979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183935868273137858061319 4775903802409706787091979)
                ·
                  refine ⟨7163855703614560180637969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775903802409706787091979 7163855703614560180637969)
                  ·
                    refine ⟨5372891777710920135478477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7163855703614560180637969 5372891777710920135478477)
                    ·
                      refine ⟨2014834416641595050804429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5372891777710920135478477 2014834416641595050804429)
                      ·
                        rfl

theorem cell23_3923876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_3923876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923876 prefixEnd_3923876 := by exact prefixLift 3923876
  have htrace : WordTrace (prefixWord ++ tailWord_3923876) baseStart_3923876 baseEnd_3923876 := by
    simpa [prefixWord, tailWord_3923876, baseEnd_3923876] using wordTrace_append hprefix tailTrace_3923876
  have hstable : (prefixWord ++ tailWord_3923876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923876).length < 2 ^ (prefixWord ++ tailWord_3923876).sum := by decide
  have hdescent : baseEnd_3923876 < baseStart_3923876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923916 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 1, 3, 2]
def baseStart_3923916 : Nat := 118140960795 + 3923916 * 2 ^ 59
def prefixEnd_3923916 : Nat := 4983230072969 + 3 ^ 40 * 3923916 * 2
def baseEnd_3923916 : Nat := 2014854955867774894304245

theorem tailTrace_3923916 : CollatzResearch.WordTrace tailWord_3923916 prefixEnd_3923916 2014854955867774894304245 := by
  unfold tailWord_3923916
  simp only [CollatzResearch.WordTrace]
  refine ⟨71558487026164979172211801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95411316034886638896282401 71558487026164979172211801)
  ·
    refine ⟨53668865269623734379158851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71558487026164979172211801 53668865269623734379158851)
    ·
      refine ⟨80503297904435601568738277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53668865269623734379158851 80503297904435601568738277)
      ·
        refine ⟨15094368357081675294138427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80503297904435601568738277 15094368357081675294138427)
        ·
          refine ⟨22641552535622512941207641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15094368357081675294138427 22641552535622512941207641)
          ·
            refine ⟨16981164401716884705905731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22641552535622512941207641 16981164401716884705905731)
            ·
              refine ⟨25471746602575327058858597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16981164401716884705905731 25471746602575327058858597)
              ·
                refine ⟨4775952487982873823535987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25471746602575327058858597 4775952487982873823535987)
                ·
                  refine ⟨7163928731974310735303981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4775952487982873823535987 7163928731974310735303981)
                  ·
                    refine ⟨2686473274490366525738993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7163928731974310735303981 2686473274490366525738993)
                    ·
                      refine ⟨2014854955867774894304245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686473274490366525738993 2014854955867774894304245)
                      ·
                        rfl

theorem cell23_3923916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_3923916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923916 prefixEnd_3923916 := by exact prefixLift 3923916
  have htrace : WordTrace (prefixWord ++ tailWord_3923916) baseStart_3923916 baseEnd_3923916 := by
    simpa [prefixWord, tailWord_3923916, baseEnd_3923916] using wordTrace_append hprefix tailTrace_3923916
  have hstable : (prefixWord ++ tailWord_3923916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923916).length < 2 ^ (prefixWord ++ tailWord_3923916).sum := by decide
  have hdescent : baseEnd_3923916 < baseStart_3923916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923946 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_3923946 : Nat := 118140960795 + 3923946 * 2 ^ 59
def prefixEnd_3923946 : Nat := 4983230072969 + 3 ^ 40 * 3923946 * 2
def baseEnd_3923946 : Nat := 2014870360287409776929107

theorem tailTrace_3923946 : CollatzResearch.WordTrace tailWord_3923946 prefixEnd_3923946 2014870360287409776929107 := by
  unfold tailWord_3923946
  simp only [CollatzResearch.WordTrace]
  refine ⟨35779517060555318367003923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95412045494814182312010461 35779517060555318367003923)
  ·
    refine ⟨53669275590832977550505885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35779517060555318367003923 53669275590832977550505885)
    ·
      refine ⟨20125978346562366581439707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53669275590832977550505885 20125978346562366581439707)
      ·
        refine ⟨30188967519843549872159561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20125978346562366581439707 30188967519843549872159561)
        ·
          refine ⟨22641725639882662404119671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30188967519843549872159561 22641725639882662404119671)
          ·
            refine ⟨33962588459823993606179507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22641725639882662404119671 33962588459823993606179507)
            ·
              refine ⟨50943882689735990409269261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33962588459823993606179507 50943882689735990409269261)
              ·
                refine ⟨19103956008650996403475973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50943882689735990409269261 19103956008650996403475973)
                ·
                  refine ⟨3581991751622061825651745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19103956008650996403475973 3581991751622061825651745)
                  ·
                    refine ⟨2686493813716546369238809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3581991751622061825651745 2686493813716546369238809)
                    ·
                      refine ⟨2014870360287409776929107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686493813716546369238809 2014870360287409776929107)
                      ·
                        rfl

theorem cell23_3923946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_3923946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923946 prefixEnd_3923946 := by exact prefixLift 3923946
  have htrace : WordTrace (prefixWord ++ tailWord_3923946) baseStart_3923946 baseEnd_3923946 := by
    simpa [prefixWord, tailWord_3923946, baseEnd_3923946] using wordTrace_append hprefix tailTrace_3923946
  have hstable : (prefixWord ++ tailWord_3923946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923946).length < 2 ^ (prefixWord ++ tailWord_3923946).sum := by decide
  have hdescent : baseEnd_3923946 < baseStart_3923946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923952 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 7]
def baseStart_3923952 : Nat := 118140960795 + 3923952 * 2 ^ 59
def prefixEnd_3923952 : Nat := 4983230072969 + 3 ^ 40 * 3923952 * 2
def baseEnd_3923952 : Nat := 223874826796815194828231

theorem tailTrace_3923952 : CollatzResearch.WordTrace tailWord_3923952 prefixEnd_3923952 223874826796815194828231 := by
  unfold tailWord_3923952
  simp only [CollatzResearch.WordTrace]
  refine ⟨71559143540099768246367055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95412191386799690995156073 71559143540099768246367055)
  ·
    refine ⟨107338715310149652369550583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71559143540099768246367055 107338715310149652369550583)
    ·
      refine ⟨161008072965224478554325875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107338715310149652369550583 161008072965224478554325875)
      ·
        refine ⟨241512109447836717831488813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161008072965224478554325875 241512109447836717831488813)
        ·
          refine ⟨90567041042938769186808305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241512109447836717831488813 90567041042938769186808305)
          ·
            refine ⟨67925280782204076890106229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90567041042938769186808305 67925280782204076890106229)
            ·
              refine ⟨6367995073331632208447459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67925280782204076890106229 6367995073331632208447459)
              ·
                refine ⟨9551992609997448312671189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367995073331632208447459 9551992609997448312671189)
                ·
                  refine ⟨223874826796815194828231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9551992609997448312671189 223874826796815194828231)
                  ·
                    rfl

theorem cell23_3923952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 7].length) (baseStart_3923952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923952 prefixEnd_3923952 := by exact prefixLift 3923952
  have htrace : WordTrace (prefixWord ++ tailWord_3923952) baseStart_3923952 baseEnd_3923952 := by
    simpa [prefixWord, tailWord_3923952, baseEnd_3923952] using wordTrace_append hprefix tailTrace_3923952
  have hstable : (prefixWord ++ tailWord_3923952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923952).length < 2 ^ (prefixWord ++ tailWord_3923952).sum := by decide
  have hdescent : baseEnd_3923952 < baseStart_3923952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923963 : List Nat := [1, 1, 1, 1, 1, 3, 8, 1, 2, 2, 2]
def baseStart_3923963 : Nat := 118140960795 + 3923963 * 2 ^ 59
def prefixEnd_3923963 : Nat := 4983230072969 + 3 ^ 40 * 3923963 * 2
def baseEnd_3923963 : Nat := 2014879089458536210416529

theorem tailTrace_3923963 : CollatzResearch.WordTrace tailWord_3923963 prefixEnd_3923963 2014879089458536210416529 := by
  unfold tailWord_3923963
  simp only [CollatzResearch.WordTrace]
  refine ⟨143118688283159685371384543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95412458855439790247589695 143118688283159685371384543)
  ·
    refine ⟨214678032424739528057076815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143118688283159685371384543 214678032424739528057076815)
    ·
      refine ⟨322017048637109292085615223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214678032424739528057076815 322017048637109292085615223)
      ·
        refine ⟨483025572955663938128422835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322017048637109292085615223 483025572955663938128422835)
        ·
          refine ⟨724538359433495907192634253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483025572955663938128422835 724538359433495907192634253)
          ·
            refine ⟨271701884787560965197237845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724538359433495907192634253 271701884787560965197237845)
            ·
              refine ⟨3184006462354230060905131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 271701884787560965197237845 3184006462354230060905131)
              ·
                refine ⟨4776009693531345091357697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184006462354230060905131 4776009693531345091357697)
                ·
                  refine ⟨3582007270148508818518273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4776009693531345091357697 3582007270148508818518273)
                  ·
                    refine ⟨2686505452611381613888705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3582007270148508818518273 2686505452611381613888705)
                    ·
                      refine ⟨2014879089458536210416529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686505452611381613888705 2014879089458536210416529)
                      ·
                        rfl

theorem cell23_3923963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 1, 2, 2, 2].length) (baseStart_3923963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923963 prefixEnd_3923963 := by exact prefixLift 3923963
  have htrace : WordTrace (prefixWord ++ tailWord_3923963) baseStart_3923963 baseEnd_3923963 := by
    simpa [prefixWord, tailWord_3923963, baseEnd_3923963] using wordTrace_append hprefix tailTrace_3923963
  have hstable : (prefixWord ++ tailWord_3923963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923963).length < 2 ^ (prefixWord ++ tailWord_3923963).sum := by decide
  have hdescent : baseEnd_3923963 < baseStart_3923963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3923992 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3923992 : Nat := 118140960795 + 3923992 * 2 ^ 59
def prefixEnd_3923992 : Nat := 4983230072969 + 3 ^ 40 * 3923992 * 2
def baseEnd_3923992 : Nat := 2014893980397516596953895

theorem tailTrace_3923992 : CollatzResearch.WordTrace tailWord_3923992 prefixEnd_3923992 2014893980397516596953895 := by
  unfold tailWord_3923992
  simp only [CollatzResearch.WordTrace]
  refine ⟨71559873000027311662095115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95413164000036415549460153 71559873000027311662095115)
  ·
    refine ⟨107339809500040967493142673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71559873000027311662095115 107339809500040967493142673)
    ·
      refine ⟨80504857125030725619857005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107339809500040967493142673 80504857125030725619857005)
      ·
        refine ⟨30189321421886522107446377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80504857125030725619857005 30189321421886522107446377)
        ·
          refine ⟨22641991066414891580584783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30189321421886522107446377 22641991066414891580584783)
          ·
            refine ⟨33962986599622337370877175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22641991066414891580584783 33962986599622337370877175)
            ·
              refine ⟨50944479899433506056315763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33962986599622337370877175 50944479899433506056315763)
              ·
                refine ⟨76416719849150259084473645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50944479899433506056315763 76416719849150259084473645)
                ·
                  refine ⟨28656269943431347156677617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76416719849150259084473645 28656269943431347156677617)
                  ·
                    refine ⟨21492202457573510367508213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28656269943431347156677617 21492202457573510367508213)
                    ·
                      refine ⟨2014893980397516596953895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21492202457573510367508213 2014893980397516596953895)
                      ·
                        rfl

theorem cell23_3923992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3923992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3923992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3923992 prefixEnd_3923992 := by exact prefixLift 3923992
  have htrace : WordTrace (prefixWord ++ tailWord_3923992) baseStart_3923992 baseEnd_3923992 := by
    simpa [prefixWord, tailWord_3923992, baseEnd_3923992] using wordTrace_append hprefix tailTrace_3923992
  have hstable : (prefixWord ++ tailWord_3923992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3923992).length < 2 ^ (prefixWord ++ tailWord_3923992).sum := by decide
  have hdescent : baseEnd_3923992 < baseStart_3923992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3923992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924019 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 1, 6, 2]
def baseStart_3924019 : Nat := 118140960795 + 3924019 * 2 ^ 59
def prefixEnd_3924019 : Nat := 4983230072969 + 3 ^ 40 * 3924019 * 2
def baseEnd_3924019 : Nat := 2014907844375187991316271

theorem tailTrace_3924019 : CollatzResearch.WordTrace tailWord_3924019 prefixEnd_3924019 2014907844375187991316271 := by
  unfold tailWord_3924019
  simp only [CollatzResearch.WordTrace]
  refine ⟨143120730770956806935423111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95413820513971204623615407 143120730770956806935423111)
  ·
    refine ⟨214681096156435210403134667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143120730770956806935423111 214681096156435210403134667)
    ·
      refine ⟨322021644234652815604702001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214681096156435210403134667 322021644234652815604702001)
      ·
        refine ⟨241516233175989611703526501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322021644234652815604702001 241516233175989611703526501)
        ·
          refine ⟨45284293720498052194411219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241516233175989611703526501 45284293720498052194411219)
          ·
            refine ⟨67926440580747078291616829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45284293720498052194411219 67926440580747078291616829)
            ·
              refine ⟨25472415217780154359356311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67926440580747078291616829 25472415217780154359356311)
              ·
                refine ⟨38208622826670231539034467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25472415217780154359356311 38208622826670231539034467)
                ·
                  refine ⟨57312934240005347308551701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38208622826670231539034467 57312934240005347308551701)
                  ·
                    refine ⟨2686543792500250655088361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57312934240005347308551701 2686543792500250655088361)
                    ·
                      refine ⟨2014907844375187991316271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686543792500250655088361 2014907844375187991316271)
                      ·
                        rfl

theorem cell23_3924019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6, 2].length) (baseStart_3924019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924019 prefixEnd_3924019 := by exact prefixLift 3924019
  have htrace : WordTrace (prefixWord ++ tailWord_3924019) baseStart_3924019 baseEnd_3924019 := by
    simpa [prefixWord, tailWord_3924019, baseEnd_3924019] using wordTrace_append hprefix tailTrace_3924019
  have hstable : (prefixWord ++ tailWord_3924019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924019).length < 2 ^ (prefixWord ++ tailWord_3924019).sum := by decide
  have hdescent : baseEnd_3924019 < baseStart_3924019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924039 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_3924039 : Nat := 118140960795 + 3924039 * 2 ^ 59
def prefixEnd_3924039 : Nat := 4983230072969 + 3 ^ 40 * 3924039 * 2
def baseEnd_3924039 : Nat := 2014918113988277913066179

theorem tailTrace_3924039 : CollatzResearch.WordTrace tailWord_3924039 prefixEnd_3924039 2014918113988277913066179 := by
  unfold tailWord_3924039
  simp only [CollatzResearch.WordTrace]
  refine ⟨143121460230884350351151171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95414306820589566900767447 143121460230884350351151171)
  ·
    refine ⟨214682190346326525526726757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143121460230884350351151171 214682190346326525526726757)
    ·
      refine ⟨40252910689936223536261267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214682190346326525526726757 40252910689936223536261267)
      ·
        refine ⟨60379366034904335304391901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40252910689936223536261267 60379366034904335304391901)
        ·
          refine ⟨22642262263089125739146963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60379366034904335304391901 22642262263089125739146963)
          ·
            refine ⟨33963393394633688608720445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22642262263089125739146963 33963393394633688608720445)
            ·
              refine ⟨12736272522987633228270167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33963393394633688608720445 12736272522987633228270167)
              ·
                refine ⟨19104408784481449842405251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736272522987633228270167 19104408784481449842405251)
                ·
                  refine ⟨28656613176722174763607877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19104408784481449842405251 28656613176722174763607877)
                  ·
                    refine ⟨5373114970635407768176477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28656613176722174763607877 5373114970635407768176477)
                    ·
                      refine ⟨2014918113988277913066179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5373114970635407768176477 2014918113988277913066179)
                      ·
                        rfl

theorem cell23_3924039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_3924039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924039 prefixEnd_3924039 := by exact prefixLift 3924039
  have htrace : WordTrace (prefixWord ++ tailWord_3924039) baseStart_3924039 baseEnd_3924039 := by
    simpa [prefixWord, tailWord_3924039, baseEnd_3924039] using wordTrace_append hprefix tailTrace_3924039
  have hstable : (prefixWord ++ tailWord_3924039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924039).length < 2 ^ (prefixWord ++ tailWord_3924039).sum := by decide
  have hdescent : baseEnd_3924039 < baseStart_3924039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924042 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 8]
def baseStart_3924042 : Nat := 118140960795 + 3924042 * 2 ^ 59
def prefixEnd_3924042 : Nat := 4983230072969 + 3 ^ 40 * 3924042 * 2
def baseEnd_3924042 : Nat := 223879961603360155703185

theorem tailTrace_3924042 : CollatzResearch.WordTrace tailWord_3924042 prefixEnd_3924042 223879961603360155703185 := by
  unfold tailWord_3924042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35780392412468370465877595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95414379766582321242340253 35780392412468370465877595)
  ·
    refine ⟨53670588618702555698816393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35780392412468370465877595 53670588618702555698816393)
    ·
      refine ⟨40252941464026916774112295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53670588618702555698816393 40252941464026916774112295)
      ·
        refine ⟨60379412196040375161168443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40252941464026916774112295 60379412196040375161168443)
        ·
          refine ⟨90569118294060562741752665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60379412196040375161168443 90569118294060562741752665)
          ·
            refine ⟨67926838720545422056314499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90569118294060562741752665 67926838720545422056314499)
            ·
              refine ⟨101890258080818133084471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67926838720545422056314499 101890258080818133084471749)
              ·
                refine ⟨19104423390153399953338453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101890258080818133084471749 19104423390153399953338453)
                ·
                  refine ⟨223879961603360155703185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19104423390153399953338453 223879961603360155703185)
                  ·
                    rfl

theorem cell23_3924042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 8].length) (baseStart_3924042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924042 prefixEnd_3924042 := by exact prefixLift 3924042
  have htrace : WordTrace (prefixWord ++ tailWord_3924042) baseStart_3924042 baseEnd_3924042 := by
    simpa [prefixWord, tailWord_3924042, baseEnd_3924042] using wordTrace_append hprefix tailTrace_3924042
  have hstable : (prefixWord ++ tailWord_3924042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924042).length < 2 ^ (prefixWord ++ tailWord_3924042).sum := by decide
  have hdescent : baseEnd_3924042 < baseStart_3924042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924076 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 6]
def baseStart_3924076 : Nat := 118140960795 + 3924076 * 2 ^ 59
def prefixEnd_3924076 : Nat := 4983230072969 + 3 ^ 40 * 3924076 * 2
def baseEnd_3924076 : Nat := 223881901419166029811501

theorem tailTrace_3924076 : CollatzResearch.WordTrace tailWord_3924076 prefixEnd_3924076 223881901419166029811501 := by
  unfold tailWord_3924076
  simp only [CollatzResearch.WordTrace]
  refine ⟨71561404865875152835124041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95415206487833537113498721 71561404865875152835124041)
  ·
    refine ⟨53671053649406364626343031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71561404865875152835124041 53671053649406364626343031)
    ·
      refine ⟨80506580474109546939514547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53671053649406364626343031 80506580474109546939514547)
      ·
        refine ⟨120759870711164320409271821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80506580474109546939514547 120759870711164320409271821)
        ·
          refine ⟨45284951516686620153476933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120759870711164320409271821 45284951516686620153476933)
          ·
            refine ⟨8490928409378741278776925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45284951516686620153476933 8490928409378741278776925)
            ·
              refine ⟨3184098153517027979541347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8490928409378741278776925 3184098153517027979541347)
              ·
                refine ⟨4776147230275541969312021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3184098153517027979541347 4776147230275541969312021)
                ·
                  refine ⟨223881901419166029811501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4776147230275541969312021 223881901419166029811501)
                  ·
                    rfl

theorem cell23_3924076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 6].length) (baseStart_3924076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924076 prefixEnd_3924076 := by exact prefixLift 3924076
  have htrace : WordTrace (prefixWord ++ tailWord_3924076) baseStart_3924076 baseEnd_3924076 := by
    simpa [prefixWord, tailWord_3924076, baseEnd_3924076] using wordTrace_append hprefix tailTrace_3924076
  have hstable : (prefixWord ++ tailWord_3924076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924076).length < 2 ^ (prefixWord ++ tailWord_3924076).sum := by decide
  have hdescent : baseEnd_3924076 < baseStart_3924076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924096 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 2, 3, 2]
def baseStart_3924096 : Nat := 118140960795 + 3924096 * 2 ^ 59
def prefixEnd_3924096 : Nat := 4983230072969 + 3 ^ 40 * 3924096 * 2
def baseEnd_3924096 : Nat := 2014947382385584190053417

theorem tailTrace_3924096 : CollatzResearch.WordTrace tailWord_3924096 prefixEnd_3924096 2014947382385584190053417 := by
  unfold tailWord_3924096
  simp only [CollatzResearch.WordTrace]
  refine ⟨71561769595838924542988071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95415692794451899390650761 71561769595838924542988071)
  ·
    refine ⟨107342654393758386814482107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71561769595838924542988071 107342654393758386814482107)
    ·
      refine ⟨161013981590637580221723161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107342654393758386814482107 161013981590637580221723161)
      ·
        refine ⟨120760486192978185166292371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161013981590637580221723161 120760486192978185166292371)
        ·
          refine ⟨181140729289467277749438557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120760486192978185166292371 181140729289467277749438557)
          ·
            refine ⟨67927773483550229156039459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181140729289467277749438557 67927773483550229156039459)
            ·
              refine ⟨101891660225325343734059189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67927773483550229156039459 101891660225325343734059189)
              ·
                refine ⟨9552343146124250975068049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101891660225325343734059189 9552343146124250975068049)
                ·
                  refine ⟨7164257359593188231301037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9552343146124250975068049 7164257359593188231301037)
                  ·
                    refine ⟨2686596509847445586737889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7164257359593188231301037 2686596509847445586737889)
                    ·
                      refine ⟨2014947382385584190053417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686596509847445586737889 2014947382385584190053417)
                      ·
                        rfl

theorem cell23_3924096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_3924096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924096 prefixEnd_3924096 := by exact prefixLift 3924096
  have htrace : WordTrace (prefixWord ++ tailWord_3924096) baseStart_3924096 baseEnd_3924096 := by
    simpa [prefixWord, tailWord_3924096, baseEnd_3924096] using wordTrace_append hprefix tailTrace_3924096
  have hstable : (prefixWord ++ tailWord_3924096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924096).length < 2 ^ (prefixWord ++ tailWord_3924096).sum := by decide
  have hdescent : baseEnd_3924096 < baseStart_3924096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924097 : List Nat := [1, 2, 4, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3924097 : Nat := 118140960795 + 3924097 * 2 ^ 59
def prefixEnd_3924097 : Nat := 4983230072969 + 3 ^ 40 * 3924097 * 2
def baseEnd_3924097 : Nat := 671649298622079562046971

theorem tailTrace_3924097 : CollatzResearch.WordTrace tailWord_3924097 prefixEnd_3924097 671649298622079562046971 := by
  unfold tailWord_3924097
  simp only [CollatzResearch.WordTrace]
  refine ⟨143123575664674226256762545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95415717109782817504508363 143123575664674226256762545)
  ·
    refine ⟨107342681748505669692571909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143123575664674226256762545 107342681748505669692571909)
    ·
      refine ⟨20126752827844813067357233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107342681748505669692571909 20126752827844813067357233)
      ·
        refine ⟨15095064620883609800517925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20126752827844813067357233 15095064620883609800517925)
        ·
          refine ⟨2830324616415676837597111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15095064620883609800517925 2830324616415676837597111)
          ·
            refine ⟨4245486924623515256395667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830324616415676837597111 4245486924623515256395667)
            ·
              refine ⟨6368230386935272884593501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245486924623515256395667 6368230386935272884593501)
              ·
                refine ⟨2388086395100727331722563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6368230386935272884593501 2388086395100727331722563)
                ·
                  refine ⟨3582129592651090997583845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388086395100727331722563 3582129592651090997583845)
                  ·
                    refine ⟨671649298622079562046971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3582129592651090997583845 671649298622079562046971)
                    ·
                      rfl

theorem cell23_3924097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3924097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924097 prefixEnd_3924097 := by exact prefixLift 3924097
  have htrace : WordTrace (prefixWord ++ tailWord_3924097) baseStart_3924097 baseEnd_3924097 := by
    simpa [prefixWord, tailWord_3924097, baseEnd_3924097] using wordTrace_append hprefix tailTrace_3924097
  have hstable : (prefixWord ++ tailWord_3924097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924097).length < 2 ^ (prefixWord ++ tailWord_3924097).sum := by decide
  have hdescent : baseEnd_3924097 < baseStart_3924097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924106 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 1, 5]
def baseStart_3924106 : Nat := 118140960795 + 3924106 * 2 ^ 59
def prefixEnd_3924106 : Nat := 4983230072969 + 3 ^ 40 * 3924106 * 2
def baseEnd_3924106 : Nat := 671650839064043050309457

theorem tailTrace_3924106 : CollatzResearch.WordTrace tailWord_3924106 prefixEnd_3924106 671650839064043050309457 := by
  unfold tailWord_3924106
  simp only [CollatzResearch.WordTrace]
  refine ⟨35780975980410405198460043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95415935947761080529226781 35780975980410405198460043)
  ·
    refine ⟨53671463970615607797690065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35780975980410405198460043 53671463970615607797690065)
    ·
      refine ⟨40253597977961705848267549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53671463970615607797690065 40253597977961705848267549)
      ·
        refine ⟨15095099241735639693100331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40253597977961705848267549 15095099241735639693100331)
        ·
          refine ⟨22642648862603459539650497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15095099241735639693100331 22642648862603459539650497)
          ·
            refine ⟨16981986646952594654737873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22642648862603459539650497 16981986646952594654737873)
            ·
              refine ⟨12736489985214445991053405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16981986646952594654737873 12736489985214445991053405)
              ·
                refine ⟨4776183744455417246645027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12736489985214445991053405 4776183744455417246645027)
                ·
                  refine ⟨7164275616683125869967541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776183744455417246645027 7164275616683125869967541)
                  ·
                    refine ⟨671650839064043050309457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7164275616683125869967541 671650839064043050309457)
                    ·
                      rfl

theorem cell23_3924106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_3924106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924106 prefixEnd_3924106 := by exact prefixLift 3924106
  have htrace : WordTrace (prefixWord ++ tailWord_3924106) baseStart_3924106 baseEnd_3924106 := by
    simpa [prefixWord, tailWord_3924106, baseEnd_3924106] using wordTrace_append hprefix tailTrace_3924106
  have hstable : (prefixWord ++ tailWord_3924106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924106).length < 2 ^ (prefixWord ++ tailWord_3924106).sum := by decide
  have hdescent : baseEnd_3924106 < baseStart_3924106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924120 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3924120 : Nat := 118140960795 + 3924120 * 2 ^ 59
def prefixEnd_3924120 : Nat := 4983230072969 + 3 ^ 40 * 3924120 * 2
def baseEnd_3924120 : Nat := 2014959705921292096153307

theorem tailTrace_3924120 : CollatzResearch.WordTrace tailWord_3924120 prefixEnd_3924120 2014959705921292096153307 := by
  unfold tailWord_3924120
  simp only [CollatzResearch.WordTrace]
  refine ⟨71562207271795450592424907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95416276362393934123233209 71562207271795450592424907)
  ·
    refine ⟨107343310907693175888637361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71562207271795450592424907 107343310907693175888637361)
    ·
      refine ⟨80507483180769881916478021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107343310907693175888637361 80507483180769881916478021)
      ·
        refine ⟨15095153096394352859339629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80507483180769881916478021 15095153096394352859339629)
        ·
          refine ⟨5660682411147882322252361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15095153096394352859339629 5660682411147882322252361)
          ·
            refine ⟨4245511808360911741689271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5660682411147882322252361 4245511808360911741689271)
            ·
              refine ⟨6368267712541367612533907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245511808360911741689271 6368267712541367612533907)
              ·
                refine ⟨9552401568812051418800861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368267712541367612533907 9552401568812051418800861)
                ·
                  refine ⟨3582150588304519282050323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9552401568812051418800861 3582150588304519282050323)
                  ·
                    refine ⟨5373225882456778923075485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3582150588304519282050323 5373225882456778923075485)
                    ·
                      refine ⟨2014959705921292096153307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5373225882456778923075485 2014959705921292096153307)
                      ·
                        rfl

theorem cell23_3924120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3924120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924120 prefixEnd_3924120 := by exact prefixLift 3924120
  have htrace : WordTrace (prefixWord ++ tailWord_3924120) baseStart_3924120 baseEnd_3924120 := by
    simpa [prefixWord, tailWord_3924120, baseEnd_3924120] using wordTrace_append hprefix tailTrace_3924120
  have hstable : (prefixWord ++ tailWord_3924120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924120).length < 2 ^ (prefixWord ++ tailWord_3924120).sum := by decide
  have hdescent : baseEnd_3924120 < baseStart_3924120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924146 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_3924146 : Nat := 118140960795 + 3924146 * 2 ^ 59
def prefixEnd_3924146 : Nat := 4983230072969 + 3 ^ 40 * 3924146 * 2
def baseEnd_3924146 : Nat := 2014973056418308994428187

theorem tailTrace_3924146 : CollatzResearch.WordTrace tailWord_3924146 prefixEnd_3924146 2014973056418308994428187 := by
  unfold tailWord_3924146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35781340710374176906324073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95416908560997805083530861 35781340710374176906324073)
  ·
    refine ⟨26836005532780632679743055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35781340710374176906324073 26836005532780632679743055)
    ·
      refine ⟨40254008299170949019614583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26836005532780632679743055 40254008299170949019614583)
      ·
        refine ⟨60381012448756423529421875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40254008299170949019614583 60381012448756423529421875)
        ·
          refine ⟨90571518673134635294132813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60381012448756423529421875 90571518673134635294132813)
          ·
            refine ⟨33964319502425488235299805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90571518673134635294132813 33964319502425488235299805)
            ·
              refine ⟨12736619813409558088237427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33964319502425488235299805 12736619813409558088237427)
              ·
                refine ⟨19104929720114337132356141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736619813409558088237427 19104929720114337132356141)
                ·
                  refine ⟨7164348645042876424633553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19104929720114337132356141 7164348645042876424633553)
                  ·
                    refine ⟨5373261483782157318475165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7164348645042876424633553 5373261483782157318475165)
                    ·
                      refine ⟨2014973056418308994428187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5373261483782157318475165 2014973056418308994428187)
                      ·
                        rfl

theorem cell23_3924146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_3924146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924146 prefixEnd_3924146 := by exact prefixLift 3924146
  have htrace : WordTrace (prefixWord ++ tailWord_3924146) baseStart_3924146 baseEnd_3924146 := by
    simpa [prefixWord, tailWord_3924146, baseEnd_3924146] using wordTrace_append hprefix tailTrace_3924146
  have hstable : (prefixWord ++ tailWord_3924146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924146).length < 2 ^ (prefixWord ++ tailWord_3924146).sum := by decide
  have hdescent : baseEnd_3924146 < baseStart_3924146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924166 : List Nat := [6, 1, 2, 14]
def baseStart_3924166 : Nat := 118140960795 + 3924166 * 2 ^ 59
def prefixEnd_3924166 : Nat := 4983230072969 + 3 ^ 40 * 3924166 * 2
def baseEnd_3924166 : Nat := 921345828089345640685

theorem tailTrace_3924166 : CollatzResearch.WordTrace tailWord_3924166 prefixEnd_3924166 921345828089345640685 := by
  unfold tailWord_3924166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472690384419507845032011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95417394867616167360682901 4472690384419507845032011)
  ·
    refine ⟨6709035576629261767548017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4472690384419507845032011 6709035576629261767548017)
    ·
      refine ⟨5031776682471946325661013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6709035576629261767548017 5031776682471946325661013)
      ·
        refine ⟨921345828089345640685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 5031776682471946325661013 921345828089345640685)
        ·
          rfl

theorem cell23_3924166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 14].length) (baseStart_3924166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924166 prefixEnd_3924166 := by exact prefixLift 3924166
  have htrace : WordTrace (prefixWord ++ tailWord_3924166) baseStart_3924166 baseEnd_3924166 := by
    simpa [prefixWord, tailWord_3924166, baseEnd_3924166] using wordTrace_append hprefix tailTrace_3924166
  have hstable : (prefixWord ++ tailWord_3924166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924166).length < 2 ^ (prefixWord ++ tailWord_3924166).sum := by decide
  have hdescent : baseEnd_3924166 < baseStart_3924166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924177 : List Nat := [1, 2, 2, 1, 2, 2, 6, 2, 1, 2, 2]
def baseStart_3924177 : Nat := 118140960795 + 3924177 * 2 ^ 59
def prefixEnd_3924177 : Nat := 4983230072969 + 3 ^ 40 * 3924177 * 2
def baseEnd_3924177 : Nat := 2014988974318598373140545

theorem tailTrace_3924177 : CollatzResearch.WordTrace tailWord_3924177 prefixEnd_3924177 2014988974318598373140545 := by
  unfold tailWord_3924177
  simp only [CollatzResearch.WordTrace]
  refine ⟨143126493504384399919674785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95417662336256266613116523 143126493504384399919674785)
  ·
    refine ⟨107344870128288299939756089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143126493504384399919674785 107344870128288299939756089)
    ·
      refine ⟨80508652596216224954817067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107344870128288299939756089 80508652596216224954817067)
      ·
        refine ⟨120762978894324337432225601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80508652596216224954817067 120762978894324337432225601)
        ·
          refine ⟨90572234170743253074169201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120762978894324337432225601 90572234170743253074169201)
          ·
            refine ⟨67929175628057439805626901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90572234170743253074169201 67929175628057439805626901)
            ·
              refine ⟨3184180107565192490888761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67929175628057439805626901 3184180107565192490888761)
              ·
                refine ⟨2388135080673894368166571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184180107565192490888761 2388135080673894368166571)
                ·
                  refine ⟨3582202621010841552249857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388135080673894368166571 3582202621010841552249857)
                  ·
                    refine ⟨2686651965758131164187393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3582202621010841552249857 2686651965758131164187393)
                    ·
                      refine ⟨2014988974318598373140545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686651965758131164187393 2014988974318598373140545)
                      ·
                        rfl

theorem cell23_3924177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_3924177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924177 prefixEnd_3924177 := by exact prefixLift 3924177
  have htrace : WordTrace (prefixWord ++ tailWord_3924177) baseStart_3924177 baseEnd_3924177 := by
    simpa [prefixWord, tailWord_3924177, baseEnd_3924177] using wordTrace_append hprefix tailTrace_3924177
  have hstable : (prefixWord ++ tailWord_3924177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924177).length < 2 ^ (prefixWord ++ tailWord_3924177).sum := by decide
  have hdescent : baseEnd_3924177 < baseStart_3924177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924193 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3924193 : Nat := 118140960795 + 3924193 * 2 ^ 59
def prefixEnd_3924193 : Nat := 4983230072969 + 3 ^ 40 * 3924193 * 2
def baseEnd_3924193 : Nat := 2014997190009070310540471

theorem tailTrace_3924193 : CollatzResearch.WordTrace tailWord_3924193 prefixEnd_3924193 2014997190009070310540471 := by
  unfold tailWord_3924193
  simp only [CollatzResearch.WordTrace]
  refine ⟨143127077072326434652257233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95418051381550956434838155 143127077072326434652257233)
  ·
    refine ⟨107345307804244825989192925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143127077072326434652257233 107345307804244825989192925)
    ·
      refine ⟨40254490426591809745947347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107345307804244825989192925 40254490426591809745947347)
      ·
        refine ⟨60381735639887714618921021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40254490426591809745947347 60381735639887714618921021)
        ·
          refine ⟨22643150864957892982095383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60381735639887714618921021 22643150864957892982095383)
          ·
            refine ⟨33964726297436839473143075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22643150864957892982095383 33964726297436839473143075)
            ·
              refine ⟨50947089446155259209714613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33964726297436839473143075 50947089446155259209714613)
              ·
                refine ⟨4776289635577055550910745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50947089446155259209714613 4776289635577055550910745)
                ·
                  refine ⟨3582217226682791663183059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4776289635577055550910745 3582217226682791663183059)
                  ·
                    refine ⟨5373325840024187494774589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3582217226682791663183059 5373325840024187494774589)
                    ·
                      refine ⟨2014997190009070310540471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5373325840024187494774589 2014997190009070310540471)
                      ·
                        rfl

theorem cell23_3924193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3924193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924193 prefixEnd_3924193 := by exact prefixLift 3924193
  have htrace : WordTrace (prefixWord ++ tailWord_3924193) baseStart_3924193 baseEnd_3924193 := by
    simpa [prefixWord, tailWord_3924193, baseEnd_3924193] using wordTrace_append hprefix tailTrace_3924193
  have hstable : (prefixWord ++ tailWord_3924193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924193).length < 2 ^ (prefixWord ++ tailWord_3924193).sum := by decide
  have hdescent : baseEnd_3924193 < baseStart_3924193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924203 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 1, 3, 2]
def baseStart_3924203 : Nat := 118140960795 + 3924203 * 2 ^ 59
def prefixEnd_3924203 : Nat := 4983230072969 + 3 ^ 40 * 3924203 * 2
def baseEnd_3924203 : Nat := 2015002324815615271415425

theorem tailTrace_3924203 : CollatzResearch.WordTrace tailWord_3924203 prefixEnd_3924203 2015002324815615271415425 := by
  unfold tailWord_3924203
  simp only [CollatzResearch.WordTrace]
  refine ⟨143127441802290206360121263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95418294534860137573414175 143127441802290206360121263)
  ·
    refine ⟨214691162703435309540181895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143127441802290206360121263 214691162703435309540181895)
    ·
      refine ⟨322036744055152964310272843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214691162703435309540181895 322036744055152964310272843)
      ·
        refine ⟨483055116082729446465409265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322036744055152964310272843 483055116082729446465409265)
        ·
          refine ⟨362291337062047084849056949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483055116082729446465409265 362291337062047084849056949)
          ·
            refine ⟨33964812849566914204599089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362291337062047084849056949 33964812849566914204599089)
            ·
              refine ⟨25473609637175185653449317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33964812849566914204599089 25473609637175185653449317)
              ·
                refine ⟨4776301806970347310021747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25473609637175185653449317 4776301806970347310021747)
                ·
                  refine ⟨7164452710455520965032621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776301806970347310021747 7164452710455520965032621)
                  ·
                    refine ⟨2686669766420820361887233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7164452710455520965032621 2686669766420820361887233)
                    ·
                      refine ⟨2015002324815615271415425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686669766420820361887233 2015002324815615271415425)
                      ·
                        rfl

theorem cell23_3924203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 3, 2].length) (baseStart_3924203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924203 prefixEnd_3924203 := by exact prefixLift 3924203
  have htrace : WordTrace (prefixWord ++ tailWord_3924203) baseStart_3924203 baseEnd_3924203 := by
    simpa [prefixWord, tailWord_3924203, baseEnd_3924203] using wordTrace_append hprefix tailTrace_3924203
  have hstable : (prefixWord ++ tailWord_3924203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924203).length < 2 ^ (prefixWord ++ tailWord_3924203).sum := by decide
  have hdescent : baseEnd_3924203 < baseStart_3924203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924220 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_3924220 : Nat := 118140960795 + 3924220 * 2 ^ 59
def prefixEnd_3924220 : Nat := 4983230072969 + 3 ^ 40 * 3924220 * 2
def baseEnd_3924220 : Nat := 2015011053986741704902847

theorem tailTrace_3924220 : CollatzResearch.WordTrace tailWord_3924220 prefixEnd_3924220 2015011053986741704902847 := by
  unfold tailWord_3924220
  simp only [CollatzResearch.WordTrace]
  refine ⟨71564030921614309131745057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95418707895485745508993409 71564030921614309131745057)
  ·
    refine ⟨53673023191210731848808793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71564030921614309131745057 53673023191210731848808793)
    ·
      refine ⟨40254767393408048886606595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53673023191210731848808793 40254767393408048886606595)
      ·
        refine ⟨60382151090112073329909893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40254767393408048886606595 60382151090112073329909893)
        ·
          refine ⟨11321653329396013749358105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60382151090112073329909893 11321653329396013749358105)
          ·
            refine ⟨8491239997047010312018579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11321653329396013749358105 8491239997047010312018579)
            ·
              refine ⟨12736859995570515468027869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8491239997047010312018579 12736859995570515468027869)
              ·
                refine ⟨4776322498338943300510451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12736859995570515468027869 4776322498338943300510451)
                ·
                  refine ⟨7164483747508414950765677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776322498338943300510451 7164483747508414950765677)
                  ·
                    refine ⟨2686681405315655606537129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7164483747508414950765677 2686681405315655606537129)
                    ·
                      refine ⟨2015011053986741704902847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686681405315655606537129 2015011053986741704902847)
                      ·
                        rfl

theorem cell23_3924220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_3924220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924220 prefixEnd_3924220 := by exact prefixLift 3924220
  have htrace : WordTrace (prefixWord ++ tailWord_3924220) baseStart_3924220 baseEnd_3924220 := by
    simpa [prefixWord, tailWord_3924220, baseEnd_3924220] using wordTrace_append hprefix tailTrace_3924220
  have hstable : (prefixWord ++ tailWord_3924220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924220).length < 2 ^ (prefixWord ++ tailWord_3924220).sum := by decide
  have hdescent : baseEnd_3924220 < baseStart_3924220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924254 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_3924254 : Nat := 118140960795 + 3924254 * 2 ^ 59
def prefixEnd_3924254 : Nat := 4983230072969 + 3 ^ 40 * 3924254 * 2
def baseEnd_3924254 : Nat := 2015028512328994571877691

theorem tailTrace_3924254 : CollatzResearch.WordTrace tailWord_3924254 prefixEnd_3924254 2015028512328994571877691 := by
  unfold tailWord_3924254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17891162740638180258778477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95419534616736961380151877 17891162740638180258778477)
  ·
    refine ⟨6709186027739317597041929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17891162740638180258778477 6709186027739317597041929)
    ·
      refine ⟨5031889520804488197781447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6709186027739317597041929 5031889520804488197781447)
      ·
        refine ⟨7547834281206732296672171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5031889520804488197781447 7547834281206732296672171)
        ·
          refine ⟨11321751421810098445008257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547834281206732296672171 11321751421810098445008257)
          ·
            refine ⟨8491313566357573833756193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11321751421810098445008257 8491313566357573833756193)
            ·
              refine ⟨6368485174768180375317145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8491313566357573833756193 6368485174768180375317145)
              ·
                refine ⟨4776363881076135281487859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368485174768180375317145 4776363881076135281487859)
                ·
                  refine ⟨7164545821614202922231789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776363881076135281487859 7164545821614202922231789)
                  ·
                    refine ⟨2686704683105326095836921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7164545821614202922231789 2686704683105326095836921)
                    ·
                      refine ⟨2015028512328994571877691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686704683105326095836921 2015028512328994571877691)
                      ·
                        rfl

theorem cell23_3924254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_3924254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924254 prefixEnd_3924254 := by exact prefixLift 3924254
  have htrace : WordTrace (prefixWord ++ tailWord_3924254) baseStart_3924254 baseEnd_3924254 := by
    simpa [prefixWord, tailWord_3924254, baseEnd_3924254] using wordTrace_append hprefix tailTrace_3924254
  have hstable : (prefixWord ++ tailWord_3924254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924254).length < 2 ^ (prefixWord ++ tailWord_3924254).sum := by decide
  have hdescent : baseEnd_3924254 < baseStart_3924254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924256 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 7]
def baseStart_3924256 : Nat := 118140960795 + 3924256 * 2 ^ 59
def prefixEnd_3924256 : Nat := 4983230072969 + 3 ^ 40 * 3924256 * 2
def baseEnd_3924256 : Nat := 223892171032255951561409

theorem tailTrace_3924256 : CollatzResearch.WordTrace tailWord_3924256 prefixEnd_3924256 223892171032255951561409 := by
  unfold tailWord_3924256
  simp only [CollatzResearch.WordTrace]
  refine ⟨71564687435549098205900311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95419583247398797607867081 71564687435549098205900311)
  ·
    refine ⟨107347031153323647308850467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71564687435549098205900311 107347031153323647308850467)
    ·
      refine ⟨161020546729985470963275701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107347031153323647308850467 161020546729985470963275701)
      ·
        refine ⟨15095676255936137902807097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161020546729985470963275701 15095676255936137902807097)
        ·
          refine ⟨11321757191952103427105323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15095676255936137902807097 11321757191952103427105323)
          ·
            refine ⟨16982635787928155140657985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11321757191952103427105323 16982635787928155140657985)
            ·
              refine ⟨12736976840946116355493489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16982635787928155140657985 12736976840946116355493489)
              ·
                refine ⟨9552732630709587266620117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12736976840946116355493489 9552732630709587266620117)
                ·
                  refine ⟨223892171032255951561409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9552732630709587266620117 223892171032255951561409)
                  ·
                    rfl

theorem cell23_3924256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_3924256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924256 prefixEnd_3924256 := by exact prefixLift 3924256
  have htrace : WordTrace (prefixWord ++ tailWord_3924256) baseStart_3924256 baseEnd_3924256 := by
    simpa [prefixWord, tailWord_3924256, baseEnd_3924256] using wordTrace_append hprefix tailTrace_3924256
  have hstable : (prefixWord ++ tailWord_3924256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924256).length < 2 ^ (prefixWord ++ tailWord_3924256).sum := by decide
  have hdescent : baseEnd_3924256 < baseStart_3924256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924270 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3924270 : Nat := 118140960795 + 3924270 * 2 ^ 59
def prefixEnd_3924270 : Nat := 4983230072969 + 3 ^ 40 * 3924270 * 2
def baseEnd_3924270 : Nat := 2015036728019466509277617

theorem tailTrace_3924270 : CollatzResearch.WordTrace tailWord_3924270 prefixEnd_3924270 2015036728019466509277617 := by
  unfold tailWord_3924270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17891235686630934600351283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95419923662031651201873509 17891235686630934600351283)
  ·
    refine ⟨26836853529946401900526925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17891235686630934600351283 26836853529946401900526925)
    ·
      refine ⟨10063820073729900712697597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26836853529946401900526925 10063820073729900712697597)
      ·
        refine ⟨3773932527648712767261599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10063820073729900712697597 3773932527648712767261599)
        ·
          refine ⟨5660898791473069150892399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3773932527648712767261599 5660898791473069150892399)
          ·
            refine ⟨8491348187209603726338599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660898791473069150892399 8491348187209603726338599)
            ·
              refine ⟨12737022280814405589507899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8491348187209603726338599 12737022280814405589507899)
              ·
                refine ⟨19105533421221608384261849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12737022280814405589507899 19105533421221608384261849)
                ·
                  refine ⟨14329150065916206288196387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19105533421221608384261849 14329150065916206288196387)
                  ·
                    refine ⟨21493725098874309432294581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14329150065916206288196387 21493725098874309432294581)
                    ·
                      refine ⟨2015036728019466509277617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21493725098874309432294581 2015036728019466509277617)
                      ·
                        rfl

theorem cell23_3924270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3924270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924270 prefixEnd_3924270 := by exact prefixLift 3924270
  have htrace : WordTrace (prefixWord ++ tailWord_3924270) baseStart_3924270 baseEnd_3924270 := by
    simpa [prefixWord, tailWord_3924270, baseEnd_3924270] using wordTrace_append hprefix tailTrace_3924270
  have hstable : (prefixWord ++ tailWord_3924270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924270).length < 2 ^ (prefixWord ++ tailWord_3924270).sum := by decide
  have hdescent : baseEnd_3924270 < baseStart_3924270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924279 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_3924279 : Nat := 118140960795 + 3924279 * 2 ^ 59
def prefixEnd_3924279 : Nat := 4983230072969 + 3 ^ 40 * 3924279 * 2
def baseEnd_3924279 : Nat := 2015041349345356974065075

theorem tailTrace_3924279 : CollatzResearch.WordTrace tailWord_3924279 prefixEnd_3924279 2015041349345356974065075 := by
  unfold tailWord_3924279
  simp only [CollatzResearch.WordTrace]
  refine ⟨143130213750014871339887891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95420142500009914226591927 143130213750014871339887891)
  ·
    refine ⟨214695320625022307009831837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143130213750014871339887891 214695320625022307009831837)
    ·
      refine ⟨80510745234383365128686939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214695320625022307009831837 80510745234383365128686939)
      ·
        refine ⟨120766117851575047693030409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80510745234383365128686939 120766117851575047693030409)
        ·
          refine ⟨90574588388681285769772807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120766117851575047693030409 90574588388681285769772807)
          ·
            refine ⟨135861882583021928654659211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90574588388681285769772807 135861882583021928654659211)
            ·
              refine ⟨203792823874532892981988817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135861882583021928654659211 203792823874532892981988817)
              ·
                refine ⟨152844617905899669736491613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203792823874532892981988817 152844617905899669736491613)
                ·
                  refine ⟨57316731714712376151184355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152844617905899669736491613 57316731714712376151184355)
                  ·
                    refine ⟨85975097572068564226776533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57316731714712376151184355 85975097572068564226776533)
                    ·
                      refine ⟨2015041349345356974065075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85975097572068564226776533 2015041349345356974065075)
                      ·
                        rfl

theorem cell23_3924279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_3924279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924279 prefixEnd_3924279 := by exact prefixLift 3924279
  have htrace : WordTrace (prefixWord ++ tailWord_3924279) baseStart_3924279 baseEnd_3924279 := by
    simpa [prefixWord, tailWord_3924279, baseEnd_3924279] using wordTrace_append hprefix tailTrace_3924279
  have hstable : (prefixWord ++ tailWord_3924279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924279).length < 2 ^ (prefixWord ++ tailWord_3924279).sum := by decide
  have hdescent : baseEnd_3924279 < baseStart_3924279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924299 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 2, 8]
def baseStart_3924299 : Nat := 118140960795 + 3924299 * 2 ^ 59
def prefixEnd_3924299 : Nat := 4983230072969 + 3 ^ 40 * 3924299 * 2
def baseEnd_3924299 : Nat := 671683872986148965271661

theorem tailTrace_3924299 : CollatzResearch.WordTrace tailWord_3924299 prefixEnd_3924299 671683872986148965271661 := by
  unfold tailWord_3924299
  simp only [CollatzResearch.WordTrace]
  refine ⟨143130943209942414755615951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95420628806628276503743967 143130943209942414755615951)
  ·
    refine ⟨214696414814913622133423927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143130943209942414755615951 214696414814913622133423927)
    ·
      refine ⟨322044622222370433200135891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214696414814913622133423927 322044622222370433200135891)
      ·
        refine ⟨483066933333555649800203837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322044622222370433200135891 483066933333555649800203837)
        ·
          refine ⟨181150100000083368675076439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483066933333555649800203837 181150100000083368675076439)
          ·
            refine ⟨271725150000125053012614659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181150100000083368675076439 271725150000125053012614659)
            ·
              refine ⟨407587725000187579518921989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271725150000125053012614659 407587725000187579518921989)
              ·
                refine ⟨76422698437535171159797873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407587725000187579518921989 76422698437535171159797873)
                ·
                  refine ⟨57317023828151378369848405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76422698437535171159797873 57317023828151378369848405)
                  ·
                    refine ⟨671683872986148965271661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57317023828151378369848405 671683872986148965271661)
                    ·
                      rfl

theorem cell23_3924299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_3924299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924299 prefixEnd_3924299 := by exact prefixLift 3924299
  have htrace : WordTrace (prefixWord ++ tailWord_3924299) baseStart_3924299 baseEnd_3924299 := by
    simpa [prefixWord, tailWord_3924299, baseEnd_3924299] using wordTrace_append hprefix tailTrace_3924299
  have hstable : (prefixWord ++ tailWord_3924299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924299).length < 2 ^ (prefixWord ++ tailWord_3924299).sum := by decide
  have hdescent : baseEnd_3924299 < baseStart_3924299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924306 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_3924306 : Nat := 118140960795 + 3924306 * 2 ^ 59
def prefixEnd_3924306 : Nat := 4983230072969 + 3 ^ 40 * 3924306 * 2
def baseEnd_3924306 : Nat := 2015055213323028368427451

theorem tailTrace_3924306 : CollatzResearch.WordTrace tailWord_3924306 prefixEnd_3924306 2015055213323028368427451 := by
  unfold tailWord_3924306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35782799630229263737780193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95420799013944703300747181 35782799630229263737780193)
  ·
    refine ⟨26837099722671947803335145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35782799630229263737780193 26837099722671947803335145)
    ·
      refine ⟨20127824792003960852501359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26837099722671947803335145 20127824792003960852501359)
      ·
        refine ⟨30191737188005941278752039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20127824792003960852501359 30191737188005941278752039)
        ·
          refine ⟨45287605782008911918128059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30191737188005941278752039 45287605782008911918128059)
          ·
            refine ⟨67931408673013367877192089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45287605782008911918128059 67931408673013367877192089)
            ·
              refine ⟨50948556504760025907894067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67931408673013367877192089 50948556504760025907894067)
              ·
                refine ⟨76422834757140038861841101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50948556504760025907894067 76422834757140038861841101)
                ·
                  refine ⟨28658563033927514573190413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76422834757140038861841101 28658563033927514573190413)
                  ·
                    refine ⟨10746961137722817964946405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28658563033927514573190413 10746961137722817964946405)
                    ·
                      refine ⟨2015055213323028368427451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10746961137722817964946405 2015055213323028368427451)
                      ·
                        rfl

theorem cell23_3924306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_3924306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924306 prefixEnd_3924306 := by exact prefixLift 3924306
  have htrace : WordTrace (prefixWord ++ tailWord_3924306) baseStart_3924306 baseEnd_3924306 := by
    simpa [prefixWord, tailWord_3924306, baseEnd_3924306] using wordTrace_append hprefix tailTrace_3924306
  have hstable : (prefixWord ++ tailWord_3924306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924306).length < 2 ^ (prefixWord ++ tailWord_3924306).sum := by decide
  have hdescent : baseEnd_3924306 < baseStart_3924306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924323 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3924323 : Nat := 118140960795 + 3924323 * 2 ^ 59
def prefixEnd_3924323 : Nat := 4983230072969 + 3 ^ 40 * 3924323 * 2
def baseEnd_3924323 : Nat := 2015063942494154801914873

theorem tailTrace_3924323 : CollatzResearch.WordTrace tailWord_3924323 prefixEnd_3924323 2015063942494154801914873 := by
  unfold tailWord_3924323
  simp only [CollatzResearch.WordTrace]
  refine ⟨143131818561855466854489623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95421212374570311236326415 143131818561855466854489623)
  ·
    refine ⟨214697727842783200281734435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143131818561855466854489623 214697727842783200281734435)
    ·
      refine ⟨322046591764174800422601653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214697727842783200281734435 322046591764174800422601653)
      ·
        refine ⟨30191867977891387539618905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322046591764174800422601653 30191867977891387539618905)
        ·
          refine ⟨22643900983418540654714179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30191867977891387539618905 22643900983418540654714179)
          ·
            refine ⟨33965851475127810982071269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22643900983418540654714179 33965851475127810982071269)
            ·
              refine ⟨6368597151586464559138363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33965851475127810982071269 6368597151586464559138363)
              ·
                refine ⟨9552895727379696838707545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368597151586464559138363 9552895727379696838707545)
                ·
                  refine ⟨7164671795534772629030659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9552895727379696838707545 7164671795534772629030659)
                  ·
                    refine ⟨10747007693302158943545989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164671795534772629030659 10747007693302158943545989)
                    ·
                      refine ⟨2015063942494154801914873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10747007693302158943545989 2015063942494154801914873)
                      ·
                        rfl

theorem cell23_3924323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3924323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924323 prefixEnd_3924323 := by exact prefixLift 3924323
  have htrace : WordTrace (prefixWord ++ tailWord_3924323) baseStart_3924323 baseEnd_3924323 := by
    simpa [prefixWord, tailWord_3924323, baseEnd_3924323] using wordTrace_append hprefix tailTrace_3924323
  have hstable : (prefixWord ++ tailWord_3924323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924323).length < 2 ^ (prefixWord ++ tailWord_3924323).sum := by decide
  have hdescent : baseEnd_3924323 < baseStart_3924323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924374 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3924374 : Nat := 118140960795 + 3924374 * 2 ^ 59
def prefixEnd_3924374 : Nat := 4983230072969 + 3 ^ 40 * 3924374 * 2
def baseEnd_3924374 : Nat := 2015090130007534102377139

theorem tailTrace_3924374 : CollatzResearch.WordTrace tailWord_3924374 prefixEnd_3924374 2015090130007534102377139 := by
  unfold tailWord_3924374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8945854917791918910287261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95422452456447135043064117 8945854917791918910287261)
  ·
    refine ⟨3354695594171969591357723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8945854917791918910287261 3354695594171969591357723)
    ·
      refine ⟨5032043391257954387036585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3354695594171969591357723 5032043391257954387036585)
      ·
        refine ⟨3774032543443465790277439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5032043391257954387036585 3774032543443465790277439)
        ·
          refine ⟨5661048815165198685416159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774032543443465790277439 5661048815165198685416159)
          ·
            refine ⟨8491573222747798028124239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661048815165198685416159 8491573222747798028124239)
            ·
              refine ⟨12737359834121697042186359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8491573222747798028124239 12737359834121697042186359)
              ·
                refine ⟨19106039751182545563279539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12737359834121697042186359 19106039751182545563279539)
                ·
                  refine ⟨28659059626773818344919309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19106039751182545563279539 28659059626773818344919309)
                  ·
                    refine ⟨10747147360040181879344741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28659059626773818344919309 10747147360040181879344741)
                    ·
                      refine ⟨2015090130007534102377139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10747147360040181879344741 2015090130007534102377139)
                      ·
                        rfl

theorem cell23_3924374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3924374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924374 prefixEnd_3924374 := by exact prefixLift 3924374
  have htrace : WordTrace (prefixWord ++ tailWord_3924374) baseStart_3924374 baseEnd_3924374 := by
    simpa [prefixWord, tailWord_3924374, baseEnd_3924374] using wordTrace_append hprefix tailTrace_3924374
  have hstable : (prefixWord ++ tailWord_3924374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924374).length < 2 ^ (prefixWord ++ tailWord_3924374).sum := by decide
  have hdescent : baseEnd_3924374 < baseStart_3924374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924397 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 6]
def baseStart_3924397 : Nat := 118140960795 + 3924397 * 2 ^ 59
def prefixEnd_3924397 : Nat := 4983230072969 + 3 ^ 40 * 3924397 * 2
def baseEnd_3924397 : Nat := 223900215562509723598837

theorem tailTrace_3924397 : CollatzResearch.WordTrace tailWord_3924397 prefixEnd_3924397 223900215562509723598837 := by
  unfold tailWord_3924397
  simp only [CollatzResearch.WordTrace]
  refine ⟨143134517563587377492683445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95423011709058251661788963 143134517563587377492683445)
  ·
    refine ⟨13418861021586316639939073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143134517563587377492683445 13418861021586316639939073)
    ·
      refine ⟨10064145766189737479954305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13418861021586316639939073 10064145766189737479954305)
      ·
        refine ⟨7548109324642303109965729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10064145766189737479954305 7548109324642303109965729)
        ·
          refine ⟨5661081993481727332474297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7548109324642303109965729 5661081993481727332474297)
          ·
            refine ⟨4245811495111295499355723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661081993481727332474297 4245811495111295499355723)
            ·
              refine ⟨6368717242666943249033585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245811495111295499355723 6368717242666943249033585)
              ·
                refine ⟨4776537932000207436775189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368717242666943249033585 4776537932000207436775189)
                ·
                  refine ⟨223900215562509723598837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4776537932000207436775189 223900215562509723598837)
                  ·
                    rfl

theorem cell23_3924397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_3924397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924397 prefixEnd_3924397 := by exact prefixLift 3924397
  have htrace : WordTrace (prefixWord ++ tailWord_3924397) baseStart_3924397 baseEnd_3924397 := by
    simpa [prefixWord, tailWord_3924397, baseEnd_3924397] using wordTrace_append hprefix tailTrace_3924397
  have hstable : (prefixWord ++ tailWord_3924397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924397).length < 2 ^ (prefixWord ++ tailWord_3924397).sum := by decide
  have hdescent : baseEnd_3924397 < baseStart_3924397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924407 : List Nat := [1, 1, 3, 1, 3, 3, 2, 4, 1, 1, 3]
def baseStart_3924407 : Nat := 118140960795 + 3924407 * 2 ^ 59
def prefixEnd_3924407 : Nat := 4983230072969 + 3 ^ 40 * 3924407 * 2
def baseEnd_3924407 : Nat := 2015107074869132473264487

theorem tailTrace_3924407 : CollatzResearch.WordTrace tailWord_3924407 prefixEnd_3924407 2015107074869132473264487 := by
  unfold tailWord_3924407
  simp only [CollatzResearch.WordTrace]
  refine ⟨143134882293551149200547475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95423254862367432800364983 143134882293551149200547475)
  ·
    refine ⟨214702323440326723800821213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143134882293551149200547475 214702323440326723800821213)
    ·
      refine ⟨80513371290122521425307955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214702323440326723800821213 80513371290122521425307955)
      ·
        refine ⟨120770056935183782137961933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80513371290122521425307955 120770056935183782137961933)
        ·
          refine ⟨45288771350693918301735725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120770056935183782137961933 45288771350693918301735725)
          ·
            refine ⟨16983289256510219363150897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45288771350693918301735725 16983289256510219363150897)
            ·
              refine ⟨12737466942382664522363173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16983289256510219363150897 12737466942382664522363173)
              ·
                refine ⟨2388275051696749597943095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12737466942382664522363173 2388275051696749597943095)
                ·
                  refine ⟨3582412577545124396914643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388275051696749597943095 3582412577545124396914643)
                  ·
                    refine ⟨5373618866317686595371965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3582412577545124396914643 5373618866317686595371965)
                    ·
                      refine ⟨2015107074869132473264487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5373618866317686595371965 2015107074869132473264487)
                      ·
                        rfl

theorem cell23_3924407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_3924407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924407 prefixEnd_3924407 := by exact prefixLift 3924407
  have htrace : WordTrace (prefixWord ++ tailWord_3924407) baseStart_3924407 baseEnd_3924407 := by
    simpa [prefixWord, tailWord_3924407, baseEnd_3924407] using wordTrace_append hprefix tailTrace_3924407
  have hstable : (prefixWord ++ tailWord_3924407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924407).length < 2 ^ (prefixWord ++ tailWord_3924407).sum := by decide
  have hdescent : baseEnd_3924407 < baseStart_3924407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924423 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 1, 6]
def baseStart_3924423 : Nat := 118140960795 + 3924423 * 2 ^ 59
def prefixEnd_3924423 : Nat := 4983230072969 + 3 ^ 40 * 3924423 * 2
def baseEnd_3924423 : Nat := 671705096853201470221471

theorem tailTrace_3924423 : CollatzResearch.WordTrace tailWord_3924423 prefixEnd_3924423 671705096853201470221471 := by
  unfold tailWord_3924423
  simp only [CollatzResearch.WordTrace]
  refine ⟨143135465861493183933129923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95423643907662122622086615 143135465861493183933129923)
  ·
    refine ⟨214703198792239775899694885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143135465861493183933129923 214703198792239775899694885)
    ·
      refine ⟨40256849773544957981192791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214703198792239775899694885 40256849773544957981192791)
      ·
        refine ⟨60385274660317436971789187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40256849773544957981192791 60385274660317436971789187)
        ·
          refine ⟨90577911990476155457683781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60385274660317436971789187 90577911990476155457683781)
          ·
            refine ⟨16983358498214279148315709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90577911990476155457683781 16983358498214279148315709)
            ·
              refine ⟨6368759436830354680618391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16983358498214279148315709 6368759436830354680618391)
              ·
                refine ⟨9553139155245532020927587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368759436830354680618391 9553139155245532020927587)
                ·
                  refine ⟨14329708732868298031391381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9553139155245532020927587 14329708732868298031391381)
                  ·
                    refine ⟨671705096853201470221471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14329708732868298031391381 671705096853201470221471)
                    ·
                      rfl

theorem cell23_3924423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_3924423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924423 prefixEnd_3924423 := by exact prefixLift 3924423
  have htrace : WordTrace (prefixWord ++ tailWord_3924423) baseStart_3924423 baseEnd_3924423 := by
    simpa [prefixWord, tailWord_3924423, baseEnd_3924423] using wordTrace_append hprefix tailTrace_3924423
  have hstable : (prefixWord ++ tailWord_3924423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924423).length < 2 ^ (prefixWord ++ tailWord_3924423).sum := by decide
  have hdescent : baseEnd_3924423 < baseStart_3924423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924433 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_3924433 : Nat := 118140960795 + 3924433 * 2 ^ 59
def prefixEnd_3924433 : Nat := 4983230072969 + 3 ^ 40 * 3924433 * 2
def baseEnd_3924433 : Nat := 2015120425366149371539367

theorem tailTrace_3924433 : CollatzResearch.WordTrace tailWord_3924433 prefixEnd_3924433 2015120425366149371539367 := by
  unfold tailWord_3924433
  simp only [CollatzResearch.WordTrace]
  refine ⟨143135830591456955640993953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95423887060971303760662635 143135830591456955640993953)
  ·
    refine ⟨107351872943592716730745465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143135830591456955640993953 107351872943592716730745465)
    ·
      refine ⟨80513904707694537548059099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107351872943592716730745465 80513904707694537548059099)
      ·
        refine ⟨120770857061541806322088649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80513904707694537548059099 120770857061541806322088649)
        ·
          refine ⟨90578142796156354741566487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120770857061541806322088649 90578142796156354741566487)
          ·
            refine ⟨135867214194234532112349731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90578142796156354741566487 135867214194234532112349731)
            ·
              refine ⟨203800821291351798168524597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135867214194234532112349731 203800821291351798168524597)
              ·
                refine ⟨19106326996064231078299181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203800821291351798168524597 19106326996064231078299181)
                ·
                  refine ⟨7164872623524086654362193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19106326996064231078299181 7164872623524086654362193)
                  ·
                    refine ⟨5373654467643064990771645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7164872623524086654362193 5373654467643064990771645)
                    ·
                      refine ⟨2015120425366149371539367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5373654467643064990771645 2015120425366149371539367)
                      ·
                        rfl

theorem cell23_3924433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_3924433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924433 prefixEnd_3924433 := by exact prefixLift 3924433
  have htrace : WordTrace (prefixWord ++ tailWord_3924433) baseStart_3924433 baseEnd_3924433 := by
    simpa [prefixWord, tailWord_3924433, baseEnd_3924433] using wordTrace_append hprefix tailTrace_3924433
  have hstable : (prefixWord ++ tailWord_3924433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924433).length < 2 ^ (prefixWord ++ tailWord_3924433).sum := by decide
  have hdescent : baseEnd_3924433 < baseStart_3924433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924484 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3924484 : Nat := 118140960795 + 3924484 * 2 ^ 59
def prefixEnd_3924484 : Nat := 4983230072969 + 3 ^ 40 * 3924484 * 2
def baseEnd_3924484 : Nat := 2015146612879528672001633

theorem tailTrace_3924484 : CollatzResearch.WordTrace tailWord_3924484 prefixEnd_3924484 2015146612879528672001633 := by
  unfold tailWord_3924484
  simp only [CollatzResearch.WordTrace]
  refine ⟨71568845357136095675550253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95425127142848127567400337 71568845357136095675550253)
  ·
    refine ⟨26838317008926035878331345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71568845357136095675550253 26838317008926035878331345)
    ·
      refine ⟨20128737756694526908748509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26838317008926035878331345 20128737756694526908748509)
      ·
        refine ⟨7548276658760447590780691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20128737756694526908748509 7548276658760447590780691)
        ·
          refine ⟨11322414988140671386171037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548276658760447590780691 11322414988140671386171037)
          ·
            refine ⟨4245905620552751769814139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11322414988140671386171037 4245905620552751769814139)
            ·
              refine ⟨6368858430829127654721209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245905620552751769814139 6368858430829127654721209)
              ·
                refine ⟨4776643823121845741040907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368858430829127654721209 4776643823121845741040907)
                ·
                  refine ⟨7164965734682768611561361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776643823121845741040907 7164965734682768611561361)
                  ·
                    refine ⟨5373724301012076458671021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7164965734682768611561361 5373724301012076458671021)
                    ·
                      refine ⟨2015146612879528672001633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5373724301012076458671021 2015146612879528672001633)
                      ·
                        rfl

theorem cell23_3924484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3924484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924484 prefixEnd_3924484 := by exact prefixLift 3924484
  have htrace : WordTrace (prefixWord ++ tailWord_3924484) baseStart_3924484 baseEnd_3924484 := by
    simpa [prefixWord, tailWord_3924484, baseEnd_3924484] using wordTrace_append hprefix tailTrace_3924484
  have hstable : (prefixWord ++ tailWord_3924484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924484).length < 2 ^ (prefixWord ++ tailWord_3924484).sum := by decide
  have hdescent : baseEnd_3924484 < baseStart_3924484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924513 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 2, 6]
def baseStart_3924513 : Nat := 118140960795 + 3924513 * 2 ^ 59
def prefixEnd_3924513 : Nat := 4983230072969 + 3 ^ 40 * 3924513 * 2
def baseEnd_3924513 : Nat := 671720501272836352846333

theorem tailTrace_3924513 : CollatzResearch.WordTrace tailWord_3924513 prefixEnd_3924513 671720501272836352846333 := by
  unfold tailWord_3924513
  simp only [CollatzResearch.WordTrace]
  refine ⟨143138748431167129303906193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95425832287444752869270795 143138748431167129303906193)
  ·
    refine ⟨107354061323375346977929645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143138748431167129303906193 107354061323375346977929645)
    ·
      refine ⟨40257772996265755116723617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107354061323375346977929645 40257772996265755116723617)
      ·
        refine ⟨30193329747199316337542713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40257772996265755116723617 30193329747199316337542713)
        ·
          refine ⟨22644997310399487253157035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30193329747199316337542713 22644997310399487253157035)
          ·
            refine ⟨33967495965599230879735553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22644997310399487253157035 33967495965599230879735553)
            ·
              refine ⟨25475621974199423159801665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33967495965599230879735553 25475621974199423159801665)
              ·
                refine ⟨19106716480649567369851249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25475621974199423159801665 19106716480649567369851249)
                ·
                  refine ⟨14330037360487175527388437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19106716480649567369851249 14330037360487175527388437)
                  ·
                    refine ⟨671720501272836352846333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14330037360487175527388437 671720501272836352846333)
                    ·
                      rfl

theorem cell23_3924513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_3924513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924513 prefixEnd_3924513 := by exact prefixLift 3924513
  have htrace : WordTrace (prefixWord ++ tailWord_3924513) baseStart_3924513 baseEnd_3924513 := by
    simpa [prefixWord, tailWord_3924513, baseEnd_3924513] using wordTrace_append hprefix tailTrace_3924513
  have hstable : (prefixWord ++ tailWord_3924513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924513).length < 2 ^ (prefixWord ++ tailWord_3924513).sum := by decide
  have hdescent : baseEnd_3924513 < baseStart_3924513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924520 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3924520 : Nat := 118140960795 + 3924520 * 2 ^ 59
def prefixEnd_3924520 : Nat := 4983230072969 + 3 ^ 40 * 3924520 * 2
def baseEnd_3924520 : Nat := 2015165098183090531151467

theorem tailTrace_3924520 : CollatzResearch.WordTrace tailWord_3924520 prefixEnd_3924520 2015165098183090531151467 := by
  unfold tailWord_3924520
  simp only [CollatzResearch.WordTrace]
  refine ⟨71569501871070884749705507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95426002494761179666274009 71569501871070884749705507)
  ·
    refine ⟨107354252806606327124558261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71569501871070884749705507 107354252806606327124558261)
    ·
      refine ⟨10064461200619343167927337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107354252806606327124558261 10064461200619343167927337)
      ·
        refine ⟨7548345900464507375945503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10064461200619343167927337 7548345900464507375945503)
        ·
          refine ⟨11322518850696761063918255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548345900464507375945503 11322518850696761063918255)
          ·
            refine ⟨16983778276045141595877383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322518850696761063918255 16983778276045141595877383)
            ·
              refine ⟨25475667414067712393816075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16983778276045141595877383 25475667414067712393816075)
              ·
                refine ⟨38213501121101568590724113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25475667414067712393816075 38213501121101568590724113)
                ·
                  refine ⟨28660125840826176443043085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38213501121101568590724113 28660125840826176443043085)
                  ·
                    refine ⟨10747547190309816166141157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28660125840826176443043085 10747547190309816166141157)
                    ·
                      refine ⟨2015165098183090531151467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10747547190309816166141157 2015165098183090531151467)
                      ·
                        rfl

theorem cell23_3924520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3924520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924520 prefixEnd_3924520 := by exact prefixLift 3924520
  have htrace : WordTrace (prefixWord ++ tailWord_3924520) baseStart_3924520 baseEnd_3924520 := by
    simpa [prefixWord, tailWord_3924520, baseEnd_3924520] using wordTrace_append hprefix tailTrace_3924520
  have hstable : (prefixWord ++ tailWord_3924520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924520).length < 2 ^ (prefixWord ++ tailWord_3924520).sum := by decide
  have hdescent : baseEnd_3924520 < baseStart_3924520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924537 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 1, 4, 2]
def baseStart_3924537 : Nat := 118140960795 + 3924537 * 2 ^ 59
def prefixEnd_3924537 : Nat := 4983230072969 + 3 ^ 40 * 3924537 * 2
def baseEnd_3924537 : Nat := 2015173827354216964638889

theorem tailTrace_3924537 : CollatzResearch.WordTrace tailWord_3924537 prefixEnd_3924537 2015173827354216964638889 := by
  unfold tailWord_3924537
  simp only [CollatzResearch.WordTrace]
  refine ⟨143139623783080181402779865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95426415855386787601853243 143139623783080181402779865)
  ·
    refine ⟨107354717837310136052084899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143139623783080181402779865 107354717837310136052084899)
    ·
      refine ⟨161032076755965204078127349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107354717837310136052084899 161032076755965204078127349)
      ·
        refine ⟨15096757195871737882324439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161032076755965204078127349 15096757195871737882324439)
        ·
          refine ⟨22645135793807606823486659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15096757195871737882324439 22645135793807606823486659)
          ·
            refine ⟨33967703690711410235229989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22645135793807606823486659 33967703690711410235229989)
            ·
              refine ⟨6368944442008389419105623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33967703690711410235229989 6368944442008389419105623)
              ·
                refine ⟨9553416663012584128658435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368944442008389419105623 9553416663012584128658435)
                ·
                  refine ⟨14330124994518876192987653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9553416663012584128658435 14330124994518876192987653)
                  ·
                    refine ⟨2686898436472289286185185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14330124994518876192987653 2686898436472289286185185)
                    ·
                      refine ⟨2015173827354216964638889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2686898436472289286185185 2015173827354216964638889)
                      ·
                        rfl

theorem cell23_3924537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_3924537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924537 prefixEnd_3924537 := by exact prefixLift 3924537
  have htrace : WordTrace (prefixWord ++ tailWord_3924537) baseStart_3924537 baseEnd_3924537 := by
    simpa [prefixWord, tailWord_3924537, baseEnd_3924537] using wordTrace_append hprefix tailTrace_3924537
  have hstable : (prefixWord ++ tailWord_3924537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924537).length < 2 ^ (prefixWord ++ tailWord_3924537).sum := by decide
  have hdescent : baseEnd_3924537 < baseStart_3924537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924543 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 7]
def baseStart_3924543 : Nat := 118140960795 + 3924543 * 2 ^ 59
def prefixEnd_3924543 : Nat := 4983230072969 + 3 ^ 40 * 3924543 * 2
def baseEnd_3924543 : Nat := 223908545359793771240429

theorem tailTrace_3924543 : CollatzResearch.WordTrace tailWord_3924543 prefixEnd_3924543 223908545359793771240429 := by
  unfold tailWord_3924543
  simp only [CollatzResearch.WordTrace]
  refine ⟨143139842621058444427498283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95426561747372296284998855 143139842621058444427498283)
  ·
    refine ⟨214709763931587666641247425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143139842621058444427498283 214709763931587666641247425)
    ·
      refine ⟨161032322948690749980935569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214709763931587666641247425 161032322948690749980935569)
      ·
        refine ⟨120774242211518062485701677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161032322948690749980935569 120774242211518062485701677)
        ·
          refine ⟨45290340829319273432138129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120774242211518062485701677 45290340829319273432138129)
          ·
            refine ⟨33967755621989455074103597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45290340829319273432138129 33967755621989455074103597)
            ·
              refine ⟨12737908358246045652788849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33967755621989455074103597 12737908358246045652788849)
              ·
                refine ⟨9553431268684534239591637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12737908358246045652788849 9553431268684534239591637)
                ·
                  refine ⟨223908545359793771240429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9553431268684534239591637 223908545359793771240429)
                  ·
                    rfl

theorem cell23_3924543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 7].length) (baseStart_3924543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924543 prefixEnd_3924543 := by exact prefixLift 3924543
  have htrace : WordTrace (prefixWord ++ tailWord_3924543) baseStart_3924543 baseEnd_3924543 := by
    simpa [prefixWord, tailWord_3924543, baseEnd_3924543] using wordTrace_append hprefix tailTrace_3924543
  have hstable : (prefixWord ++ tailWord_3924543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924543).length < 2 ^ (prefixWord ++ tailWord_3924543).sum := by decide
  have hdescent : baseEnd_3924543 < baseStart_3924543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924583 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3924583 : Nat := 118140960795 + 3924583 * 2 ^ 59
def prefixEnd_3924583 : Nat := 4983230072969 + 3 ^ 40 * 3924583 * 2
def baseEnd_3924583 : Nat := 2015197447464323784663677

theorem tailTrace_3924583 : CollatzResearch.WordTrace tailWord_3924583 prefixEnd_3924583 2015197447464323784663677 := by
  unfold tailWord_3924583
  simp only [CollatzResearch.WordTrace]
  refine ⟨143141301540913531258954403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95427534360609020839302935 143141301540913531258954403)
  ·
    refine ⟨214711952311370296888431605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143141301540913531258954403 214711952311370296888431605)
    ·
      refine ⟨20129245529190965333290463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214711952311370296888431605 20129245529190965333290463)
      ·
        refine ⟨30193868293786447999935695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20129245529190965333290463 30193868293786447999935695)
        ·
          refine ⟨45290802440679671999903543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30193868293786447999935695 45290802440679671999903543)
          ·
            refine ⟨67936203661019507999855315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45290802440679671999903543 67936203661019507999855315)
            ·
              refine ⟨101904305491529261999782973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67936203661019507999855315 101904305491529261999782973)
              ·
                refine ⟨38214114559323473249918615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101904305491529261999782973 38214114559323473249918615)
                ·
                  refine ⟨57321171838985209874877923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38214114559323473249918615 57321171838985209874877923)
                  ·
                    refine ⟨85981757758477814812316885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57321171838985209874877923 85981757758477814812316885)
                    ·
                      refine ⟨2015197447464323784663677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85981757758477814812316885 2015197447464323784663677)
                      ·
                        rfl

theorem cell23_3924583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3924583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924583 prefixEnd_3924583 := by exact prefixLift 3924583
  have htrace : WordTrace (prefixWord ++ tailWord_3924583) baseStart_3924583 baseEnd_3924583 := by
    simpa [prefixWord, tailWord_3924583, baseEnd_3924583] using wordTrace_append hprefix tailTrace_3924583
  have hstable : (prefixWord ++ tailWord_3924583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924583).length < 2 ^ (prefixWord ++ tailWord_3924583).sum := by decide
  have hdescent : baseEnd_3924583 < baseStart_3924583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924590 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3924590 : Nat := 118140960795 + 3924590 * 2 ^ 59
def prefixEnd_3924590 : Nat := 4983230072969 + 3 ^ 40 * 3924590 * 2
def baseEnd_3924590 : Nat := 671733680609635085758715

theorem tailTrace_3924590 : CollatzResearch.WordTrace tailWord_3924590 prefixEnd_3924590 671733680609635085758715 := by
  unfold tailWord_3924590
  simp only [CollatzResearch.WordTrace]
  refine ⟨17892694606486021431807403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95427704567925447636306149 17892694606486021431807403)
  ·
    refine ⟨26839041909729032147711105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17892694606486021431807403 26839041909729032147711105)
    ·
      refine ⟨20129281432296774110783329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26839041909729032147711105 20129281432296774110783329)
      ·
        refine ⟨15096961074222580583087497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20129281432296774110783329 15096961074222580583087497)
        ·
          refine ⟨11322720805666935437315623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15096961074222580583087497 11322720805666935437315623)
          ·
            refine ⟨16984081208500403155973435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322720805666935437315623 16984081208500403155973435)
            ·
              refine ⟨25476121812750604733960153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16984081208500403155973435 25476121812750604733960153)
              ·
                refine ⟨19107091359562953550470115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25476121812750604733960153 19107091359562953550470115)
                ·
                  refine ⟨28660637039344430325705173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19107091359562953550470115 28660637039344430325705173)
                  ·
                    refine ⟨671733680609635085758715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28660637039344430325705173 671733680609635085758715)
                    ·
                      rfl

theorem cell23_3924590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3924590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924590 prefixEnd_3924590 := by exact prefixLift 3924590
  have htrace : WordTrace (prefixWord ++ tailWord_3924590) baseStart_3924590 baseEnd_3924590 := by
    simpa [prefixWord, tailWord_3924590, baseEnd_3924590] using wordTrace_append hprefix tailTrace_3924590
  have hstable : (prefixWord ++ tailWord_3924590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924590).length < 2 ^ (prefixWord ++ tailWord_3924590).sum := by decide
  have hdescent : baseEnd_3924590 < baseStart_3924590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924623 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_3924623 : Nat := 118140960795 + 3924623 * 2 ^ 59
def prefixEnd_3924623 : Nat := 4983230072969 + 3 ^ 40 * 3924623 * 2
def baseEnd_3924623 : Nat := 2015217986690503628163493

theorem tailTrace_3924623 : CollatzResearch.WordTrace tailWord_3924623 prefixEnd_3924623 2015217986690503628163493 := by
  unfold tailWord_3924623
  simp only [CollatzResearch.WordTrace]
  refine ⟨143142760460768618090410523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95428506973845745393607015 143142760460768618090410523)
  ·
    refine ⟨214714140691152927135615785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143142760460768618090410523 214714140691152927135615785)
    ·
      refine ⟨161035605518364695351711839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214714140691152927135615785 161035605518364695351711839)
      ·
        refine ⟨241553408277547043027567759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161035605518364695351711839 241553408277547043027567759)
        ·
          refine ⟨362330112416320564541351639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241553408277547043027567759 362330112416320564541351639)
          ·
            refine ⟨543495168624480846812027459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362330112416320564541351639 543495168624480846812027459)
            ·
              refine ⟨815242752936721270218041189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543495168624480846812027459 815242752936721270218041189)
              ·
                refine ⟨152858016175635238165882723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815242752936721270218041189 152858016175635238165882723)
                ·
                  refine ⟨229287024263452857248824085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152858016175635238165882723 229287024263452857248824085)
                  ·
                    refine ⟨10747829262349352683538629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 229287024263452857248824085 10747829262349352683538629)
                    ·
                      refine ⟨2015217986690503628163493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10747829262349352683538629 2015217986690503628163493)
                      ·
                        rfl

theorem cell23_3924623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_3924623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924623 prefixEnd_3924623 := by exact prefixLift 3924623
  have htrace : WordTrace (prefixWord ++ tailWord_3924623) baseStart_3924623 baseEnd_3924623 := by
    simpa [prefixWord, tailWord_3924623, baseEnd_3924623] using wordTrace_append hprefix tailTrace_3924623
  have hstable : (prefixWord ++ tailWord_3924623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924623).length < 2 ^ (prefixWord ++ tailWord_3924623).sum := by decide
  have hdescent : baseEnd_3924623 < baseStart_3924623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924633 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 8]
def baseStart_3924633 : Nat := 118140960795 + 3924633 * 2 ^ 59
def prefixEnd_3924633 : Nat := 4983230072969 + 3 ^ 40 * 3924633 * 2
def baseEnd_3924633 : Nat := 223913680166338732115383

theorem tailTrace_3924633 : CollatzResearch.WordTrace tailWord_3924633 prefixEnd_3924633 223913680166338732115383 := by
  unfold tailWord_3924633
  simp only [CollatzResearch.WordTrace]
  refine ⟨143143125190732389798274553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95428750127154926532183035 143143125190732389798274553)
  ·
    refine ⟨107357343893049292348705915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143143125190732389798274553 107357343893049292348705915)
    ·
      refine ⟨161036015839573938523058873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107357343893049292348705915 161036015839573938523058873)
      ·
        refine ⟨120777011879680453892294155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161036015839573938523058873 120777011879680453892294155)
        ·
          refine ⟨181165517819520680838441233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120777011879680453892294155 181165517819520680838441233)
          ·
            refine ⟨135874138364640510628830925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181165517819520680838441233 135874138364640510628830925)
            ·
              refine ⟨50952801886740191485811597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135874138364640510628830925 50952801886740191485811597)
              ·
                refine ⟨19107300707527571807179349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50952801886740191485811597 19107300707527571807179349)
                ·
                  refine ⟨223913680166338732115383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19107300707527571807179349 223913680166338732115383)
                  ·
                    rfl

theorem cell23_3924633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_3924633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924633 prefixEnd_3924633 := by exact prefixLift 3924633
  have htrace : WordTrace (prefixWord ++ tailWord_3924633) baseStart_3924633 baseEnd_3924633 := by
    simpa [prefixWord, tailWord_3924633, baseEnd_3924633] using wordTrace_append hprefix tailTrace_3924633
  have hstable : (prefixWord ++ tailWord_3924633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924633).length < 2 ^ (prefixWord ++ tailWord_3924633).sum := by decide
  have hdescent : baseEnd_3924633 < baseStart_3924633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924637 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3924637 : Nat := 118140960795 + 3924637 * 2 ^ 59
def prefixEnd_3924637 : Nat := 4983230072969 + 3 ^ 40 * 3924637 * 2
def baseEnd_3924637 : Nat := 671741725139888857796143

theorem tailTrace_3924637 : CollatzResearch.WordTrace tailWord_3924637 prefixEnd_3924637 671741725139888857796143 := by
  unfold tailWord_3924637
  simp only [CollatzResearch.WordTrace]
  refine ⟨143143271082717898481420165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95428847388478598987613443 143143271082717898481420165)
  ·
    refine ⟨26839363328009605965266281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143143271082717898481420165 26839363328009605965266281)
    ·
      refine ⟨20129522496007204473949711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26839363328009605965266281 20129522496007204473949711)
      ·
        refine ⟨30194283744010806710924567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20129522496007204473949711 30194283744010806710924567)
        ·
          refine ⟨45291425616016210066386851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30194283744010806710924567 45291425616016210066386851)
          ·
            refine ⟨67937138424024315099580277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45291425616016210066386851 67937138424024315099580277)
            ·
              refine ⟨6369106727252279540585651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67937138424024315099580277 6369106727252279540585651)
              ·
                refine ⟨9553660090878419310878477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369106727252279540585651 9553660090878419310878477)
                ·
                  refine ⟨3582622534079407241579429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9553660090878419310878477 3582622534079407241579429)
                  ·
                    refine ⟨671741725139888857796143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3582622534079407241579429 671741725139888857796143)
                    ·
                      rfl

theorem cell23_3924637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3924637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924637 prefixEnd_3924637 := by exact prefixLift 3924637
  have htrace : WordTrace (prefixWord ++ tailWord_3924637) baseStart_3924637 baseEnd_3924637 := by
    simpa [prefixWord, tailWord_3924637, baseEnd_3924637] using wordTrace_append hprefix tailTrace_3924637
  have hstable : (prefixWord ++ tailWord_3924637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924637).length < 2 ^ (prefixWord ++ tailWord_3924637).sum := by decide
  have hdescent : baseEnd_3924637 < baseStart_3924637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924717 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3924717 : Nat := 118140960795 + 3924717 * 2 ^ 59
def prefixEnd_3924717 : Nat := 4983230072969 + 3 ^ 40 * 3924717 * 2
def baseEnd_3924717 : Nat := 2015266253872026260388061

theorem tailTrace_3924717 : CollatzResearch.WordTrace tailWord_3924717 prefixEnd_3924717 2015266253872026260388061 := by
  unfold tailWord_3924717
  simp only [CollatzResearch.WordTrace]
  refine ⟨143146188922428072144332405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95430792614952048096221603 143146188922428072144332405)
  ·
    refine ⟨13419955211477631763531163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143146188922428072144332405 13419955211477631763531163)
    ·
      refine ⟨20129932817216447645296745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13419955211477631763531163 20129932817216447645296745)
      ·
        refine ⟨15097449612912335733972559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20129932817216447645296745 15097449612912335733972559)
        ·
          refine ⟨22646174419368503600958839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15097449612912335733972559 22646174419368503600958839)
          ·
            refine ⟨33969261629052755401438259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22646174419368503600958839 33969261629052755401438259)
            ·
              refine ⟨50953892443579133102157389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33969261629052755401438259 50953892443579133102157389)
              ·
                refine ⟨19107709666342174913309021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50953892443579133102157389 19107709666342174913309021)
                ·
                  refine ⟨7165391124878315592490883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19107709666342174913309021 7165391124878315592490883)
                  ·
                    refine ⟨10748086687317473388736325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7165391124878315592490883 10748086687317473388736325)
                    ·
                      refine ⟨2015266253872026260388061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10748086687317473388736325 2015266253872026260388061)
                      ·
                        rfl

theorem cell23_3924717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3924717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924717 prefixEnd_3924717 := by exact prefixLift 3924717
  have htrace : WordTrace (prefixWord ++ tailWord_3924717) baseStart_3924717 baseEnd_3924717 := by
    simpa [prefixWord, tailWord_3924717, baseEnd_3924717] using wordTrace_append hprefix tailTrace_3924717
  have hstable : (prefixWord ++ tailWord_3924717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924717).length < 2 ^ (prefixWord ++ tailWord_3924717).sum := by decide
  have hdescent : baseEnd_3924717 < baseStart_3924717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924740 : List Nat := [2, 3, 2, 2, 1, 1, 12]
def baseStart_3924740 : Nat := 118140960795 + 3924740 * 2 ^ 59
def prefixEnd_3924740 : Nat := 4983230072969 + 3 ^ 40 * 3924740 * 2
def baseEnd_3924740 : Nat := 24879976097865181116055

theorem tailTrace_3924740 : CollatzResearch.WordTrace tailWord_3924740 prefixEnd_3924740 24879976097865181116055 := by
  unfold tailWord_3924740
  simp only [CollatzResearch.WordTrace]
  refine ⟨71573513900672373536209837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95431351867563164714946449 71573513900672373536209837)
  ·
    refine ⟨26840067712752140076078689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71573513900672373536209837 26840067712752140076078689)
    ·
      refine ⟨20130050784564105057059017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26840067712752140076078689 20130050784564105057059017)
      ·
        refine ⟨15097538088423078792794263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20130050784564105057059017 15097538088423078792794263)
        ·
          refine ⟨22646307132634618189191395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15097538088423078792794263 22646307132634618189191395)
          ·
            refine ⟨33969460698951927283787093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22646307132634618189191395 33969460698951927283787093)
            ·
              refine ⟨24879976097865181116055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 33969460698951927283787093 24879976097865181116055)
              ·
                rfl

theorem cell23_3924740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 12].length) (baseStart_3924740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924740 prefixEnd_3924740 := by exact prefixLift 3924740
  have htrace : WordTrace (prefixWord ++ tailWord_3924740) baseStart_3924740 baseEnd_3924740 := by
    simpa [prefixWord, tailWord_3924740, baseEnd_3924740] using wordTrace_append hprefix tailTrace_3924740
  have hstable : (prefixWord ++ tailWord_3924740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924740).length < 2 ^ (prefixWord ++ tailWord_3924740).sum := by decide
  have hdescent : baseEnd_3924740 < baseStart_3924740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924744 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 2, 4]
def baseStart_3924744 : Nat := 118140960795 + 3924744 * 2 ^ 59
def prefixEnd_3924744 : Nat := 4983230072969 + 3 ^ 40 * 3924744 * 2
def baseEnd_3924744 : Nat := 671760039283232551583479

theorem tailTrace_3924744 : CollatzResearch.WordTrace tailWord_3924744 prefixEnd_3924744 671760039283232551583479 := by
  unfold tailWord_3924744
  simp only [CollatzResearch.WordTrace]
  refine ⟨71573586846665127877782643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95431449128886837170376857 71573586846665127877782643)
  ·
    refine ⟨107360380269997691816673965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71573586846665127877782643 107360380269997691816673965)
    ·
      refine ⟨40260142601249134431252737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107360380269997691816673965 40260142601249134431252737)
      ·
        refine ⟨30195106950936850823439553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40260142601249134431252737 30195106950936850823439553)
        ·
          refine ⟨22646330213202638117579665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30195106950936850823439553 22646330213202638117579665)
          ·
            refine ⟨16984747659901978588184749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22646330213202638117579665 16984747659901978588184749)
            ·
              refine ⟨6369280372463241970569281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16984747659901978588184749 6369280372463241970569281)
              ·
                refine ⟨4776960279347431477926961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369280372463241970569281 4776960279347431477926961)
                ·
                  refine ⟨3582720209510573608445221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4776960279347431477926961 3582720209510573608445221)
                  ·
                    refine ⟨671760039283232551583479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3582720209510573608445221 671760039283232551583479)
                    ·
                      rfl

theorem cell23_3924744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_3924744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924744 prefixEnd_3924744 := by exact prefixLift 3924744
  have htrace : WordTrace (prefixWord ++ tailWord_3924744) baseStart_3924744 baseEnd_3924744 := by
    simpa [prefixWord, tailWord_3924744, baseEnd_3924744] using wordTrace_append hprefix tailTrace_3924744
  have hstable : (prefixWord ++ tailWord_3924744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924744).length < 2 ^ (prefixWord ++ tailWord_3924744).sum := by decide
  have hdescent : baseEnd_3924744 < baseStart_3924744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924750 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3924750 : Nat := 118140960795 + 3924750 * 2 ^ 59
def prefixEnd_3924750 : Nat := 4983230072969 + 3 ^ 40 * 3924750 * 2
def baseEnd_3924750 : Nat := 2015283198733624631275409

theorem tailTrace_3924750 : CollatzResearch.WordTrace tailWord_3924750 prefixEnd_3924750 2015283198733624631275409 := by
  unfold tailWord_3924750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17893424066413564847535463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95431595020872345853522469 17893424066413564847535463)
  ·
    refine ⟨26840136099620347271303195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17893424066413564847535463 26840136099620347271303195)
    ·
      refine ⟨40260204149430520906954793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26840136099620347271303195 40260204149430520906954793)
      ·
        refine ⟨30195153112072890680216095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40260204149430520906954793 30195153112072890680216095)
        ·
          refine ⟨45292729668109336020324143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30195153112072890680216095 45292729668109336020324143)
          ·
            refine ⟨67939094502164004030486215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45292729668109336020324143 67939094502164004030486215)
            ·
              refine ⟨101908641753246006045729323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67939094502164004030486215 101908641753246006045729323)
              ·
                refine ⟨152862962629869009068593985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101908641753246006045729323 152862962629869009068593985)
                ·
                  refine ⟨114647221972401756801445489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152862962629869009068593985 114647221972401756801445489)
                  ·
                    refine ⟨85985416479301317601084117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114647221972401756801445489 85985416479301317601084117)
                    ·
                      refine ⟨2015283198733624631275409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85985416479301317601084117 2015283198733624631275409)
                      ·
                        rfl

theorem cell23_3924750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3924750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924750 prefixEnd_3924750 := by exact prefixLift 3924750
  have htrace : WordTrace (prefixWord ++ tailWord_3924750) baseStart_3924750 baseEnd_3924750 := by
    simpa [prefixWord, tailWord_3924750, baseEnd_3924750] using wordTrace_append hprefix tailTrace_3924750
  have hstable : (prefixWord ++ tailWord_3924750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924750).length < 2 ^ (prefixWord ++ tailWord_3924750).sum := by decide
  have hdescent : baseEnd_3924750 < baseStart_3924750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924751 : List Nat := [1, 1, 2, 1, 1, 1, 5, 6, 1, 2, 2]
def baseStart_3924751 : Nat := 118140960795 + 3924751 * 2 ^ 59
def prefixEnd_3924751 : Nat := 4983230072969 + 3 ^ 40 * 3924751 * 2
def baseEnd_3924751 : Nat := 2015283712214279127362905

theorem tailTrace_3924751 : CollatzResearch.WordTrace tailWord_3924751 prefixEnd_3924751 2015283712214279127362905 := by
  unfold tailWord_3924751
  simp only [CollatzResearch.WordTrace]
  refine ⟨143147429004304895951070107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95431619336203263967380071 143147429004304895951070107)
  ·
    refine ⟨214721143506457343926605161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143147429004304895951070107 214721143506457343926605161)
    ·
      refine ⟨161040857629843007944953871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214721143506457343926605161 161040857629843007944953871)
      ·
        refine ⟨241561286444764511917430807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161040857629843007944953871 241561286444764511917430807)
        ·
          refine ⟨362341929667146767876146211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241561286444764511917430807 362341929667146767876146211)
          ·
            refine ⟨543512894500720151814219317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362341929667146767876146211 543512894500720151814219317)
            ·
              refine ⟨50954333859442514232583061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 543512894500720151814219317 50954333859442514232583061)
              ·
                refine ⟨2388484399661367854652331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50954333859442514232583061 2388484399661367854652331)
                ·
                  refine ⟨3582726599492051781978497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388484399661367854652331 3582726599492051781978497)
                  ·
                    refine ⟨2687044949619038836483873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3582726599492051781978497 2687044949619038836483873)
                    ·
                      refine ⟨2015283712214279127362905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2687044949619038836483873 2015283712214279127362905)
                      ·
                        rfl

theorem cell23_3924751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 1, 2, 2].length) (baseStart_3924751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924751 prefixEnd_3924751 := by exact prefixLift 3924751
  have htrace : WordTrace (prefixWord ++ tailWord_3924751) baseStart_3924751 baseEnd_3924751 := by
    simpa [prefixWord, tailWord_3924751, baseEnd_3924751] using wordTrace_append hprefix tailTrace_3924751
  have hstable : (prefixWord ++ tailWord_3924751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924751).length < 2 ^ (prefixWord ++ tailWord_3924751).sum := by decide
  have hdescent : baseEnd_3924751 < baseStart_3924751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924764 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3924764 : Nat := 118140960795 + 3924764 * 2 ^ 59
def prefixEnd_3924764 : Nat := 4983230072969 + 3 ^ 40 * 3924764 * 2
def baseEnd_3924764 : Nat := 2015290387462787576500345

theorem tailTrace_3924764 : CollatzResearch.WordTrace tailWord_3924764 prefixEnd_3924764 2015290387462787576500345 := by
  unfold tailWord_3924764
  simp only [CollatzResearch.WordTrace]
  refine ⟨71573951576628899585646673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95431935435505199447528897 71573951576628899585646673)
  ·
    refine ⟨53680463682471674689235005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71573951576628899585646673 53680463682471674689235005)
    ·
      refine ⟨20130173880926878008463127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53680463682471674689235005 20130173880926878008463127)
      ·
        refine ⟨30195260821390317012694691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20130173880926878008463127 30195260821390317012694691)
        ·
          refine ⟨45292891232085475519042037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30195260821390317012694691 45292891232085475519042037)
          ·
            refine ⟨4246208553008013329910191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45292891232085475519042037 4246208553008013329910191)
            ·
              refine ⟨6369312829512019994865287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246208553008013329910191 6369312829512019994865287)
              ·
                refine ⟨9553969244268029992297931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369312829512019994865287 9553969244268029992297931)
                ·
                  refine ⟨14330953866402044988446897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9553969244268029992297931 14330953866402044988446897)
                  ·
                    refine ⟨10748215399801533741335173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14330953866402044988446897 10748215399801533741335173)
                    ·
                      refine ⟨2015290387462787576500345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10748215399801533741335173 2015290387462787576500345)
                      ·
                        rfl

theorem cell23_3924764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3924764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924764 prefixEnd_3924764 := by exact prefixLift 3924764
  have htrace : WordTrace (prefixWord ++ tailWord_3924764) baseStart_3924764 baseEnd_3924764 := by
    simpa [prefixWord, tailWord_3924764, baseEnd_3924764] using wordTrace_append hprefix tailTrace_3924764
  have hstable : (prefixWord ++ tailWord_3924764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924764).length < 2 ^ (prefixWord ++ tailWord_3924764).sum := by decide
  have hdescent : baseEnd_3924764 < baseStart_3924764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924780 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 5]
def baseStart_3924780 : Nat := 118140960795 + 3924780 * 2 ^ 59
def prefixEnd_3924780 : Nat := 4983230072969 + 3 ^ 40 * 3924780 * 2
def baseEnd_3924780 : Nat := 2015298603153259513900271

theorem tailTrace_3924780 : CollatzResearch.WordTrace tailWord_3924780 prefixEnd_3924780 2015298603153259513900271 := by
  unfold tailWord_3924780
  simp only [CollatzResearch.WordTrace]
  refine ⟨71574243360599916951937897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95432324480799889269250529 71574243360599916951937897)
  ·
    refine ⟨53680682520449937713953423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71574243360599916951937897 53680682520449937713953423)
    ·
      refine ⟨80521023780674906570930135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53680682520449937713953423 80521023780674906570930135)
      ·
        refine ⟨120781535671012359856395203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80521023780674906570930135 120781535671012359856395203)
        ·
          refine ⟨181172303506518539784592805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120781535671012359856395203 181172303506518539784592805)
          ·
            refine ⟨33969806907472226209611151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181172303506518539784592805 33969806907472226209611151)
            ·
              refine ⟨50954710361208339314416727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33969806907472226209611151 50954710361208339314416727)
              ·
                refine ⟨76432065541812508971625091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50954710361208339314416727 76432065541812508971625091)
                ·
                  refine ⟨114648098312718763457437637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76432065541812508971625091 114648098312718763457437637)
                  ·
                    refine ⟨21496518433634768148269557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114648098312718763457437637 21496518433634768148269557)
                    ·
                      refine ⟨2015298603153259513900271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21496518433634768148269557 2015298603153259513900271)
                      ·
                        rfl

theorem cell23_3924780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_3924780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924780 prefixEnd_3924780 := by exact prefixLift 3924780
  have htrace : WordTrace (prefixWord ++ tailWord_3924780) baseStart_3924780 baseEnd_3924780 := by
    simpa [prefixWord, tailWord_3924780, baseEnd_3924780] using wordTrace_append hprefix tailTrace_3924780
  have hstable : (prefixWord ++ tailWord_3924780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924780).length < 2 ^ (prefixWord ++ tailWord_3924780).sum := by decide
  have hdescent : baseEnd_3924780 < baseStart_3924780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924800 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 4, 6]
def baseStart_3924800 : Nat := 118140960795 + 3924800 * 2 ^ 59
def prefixEnd_3924800 : Nat := 4983230072969 + 3 ^ 40 * 3924800 * 2
def baseEnd_3924800 : Nat := 671769624255449811883393

theorem tailTrace_3924800 : CollatzResearch.WordTrace tailWord_3924800 prefixEnd_3924800 671769624255449811883393 := by
  unfold tailWord_3924800
  simp only [CollatzResearch.WordTrace]
  refine ⟨71574608090563688659801927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95432810787418251546402569 71574608090563688659801927)
  ·
    refine ⟨107361912135845532989702891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71574608090563688659801927 107361912135845532989702891)
    ·
      refine ⟨161042868203768299484554337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107361912135845532989702891 161042868203768299484554337)
      ·
        refine ⟨120782151152826224613415753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161042868203768299484554337 120782151152826224613415753)
        ·
          refine ⟨90586613364619668460061815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120782151152826224613415753 90586613364619668460061815)
          ·
            refine ⟨135879920046929502690092723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90586613364619668460061815 135879920046929502690092723)
            ·
              refine ⟨203819880070394254035139085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135879920046929502690092723 203819880070394254035139085)
              ·
                refine ⟨76432455026397845263177157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203819880070394254035139085 76432455026397845263177157)
                ·
                  refine ⟨14331085317449595986845717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76432455026397845263177157 14331085317449595986845717)
                  ·
                    refine ⟨671769624255449811883393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14331085317449595986845717 671769624255449811883393)
                    ·
                      rfl

theorem cell23_3924800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_3924800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924800 prefixEnd_3924800 := by exact prefixLift 3924800
  have htrace : WordTrace (prefixWord ++ tailWord_3924800) baseStart_3924800 baseEnd_3924800 := by
    simpa [prefixWord, tailWord_3924800, baseEnd_3924800] using wordTrace_append hprefix tailTrace_3924800
  have hstable : (prefixWord ++ tailWord_3924800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924800).length < 2 ^ (prefixWord ++ tailWord_3924800).sum := by decide
  have hdescent : baseEnd_3924800 < baseStart_3924800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924828 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3924828 : Nat := 118140960795 + 3924828 * 2 ^ 59
def prefixEnd_3924828 : Nat := 4983230072969 + 3 ^ 40 * 3924828 * 2
def baseEnd_3924828 : Nat := 2015323250224675326100051

theorem tailTrace_3924828 : CollatzResearch.WordTrace tailWord_3924828 prefixEnd_3924828 2015323250224675326100051 := by
  unfold tailWord_3924828
  simp only [CollatzResearch.WordTrace]
  refine ⟨71575118712512969050811569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95433491616683958734415425 71575118712512969050811569)
  ·
    refine ⟨53681339034384726788108677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71575118712512969050811569 53681339034384726788108677)
    ·
      refine ⟨10065251068947136272770377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53681339034384726788108677 10065251068947136272770377)
      ·
        refine ⟨7548938301710352204577783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10065251068947136272770377 7548938301710352204577783)
        ·
          refine ⟨11323407452565528306866675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7548938301710352204577783 11323407452565528306866675)
          ·
            refine ⟨16985111178848292460300013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11323407452565528306866675 16985111178848292460300013)
            ·
              refine ⟨6369416692068109672612505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16985111178848292460300013 6369416692068109672612505)
              ·
                refine ⟨4777062519051082254459379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369416692068109672612505 4777062519051082254459379)
                ·
                  refine ⟨7165593778576623381689069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777062519051082254459379 7165593778576623381689069)
                  ·
                    refine ⟨2687097666966233768133401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7165593778576623381689069 2687097666966233768133401)
                    ·
                      refine ⟨2015323250224675326100051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2687097666966233768133401 2015323250224675326100051)
                      ·
                        rfl

theorem cell23_3924828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3924828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924828 prefixEnd_3924828 := by exact prefixLift 3924828
  have htrace : WordTrace (prefixWord ++ tailWord_3924828) baseStart_3924828 baseEnd_3924828 := by
    simpa [prefixWord, tailWord_3924828, baseEnd_3924828] using wordTrace_append hprefix tailTrace_3924828
  have hstable : (prefixWord ++ tailWord_3924828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924828).length < 2 ^ (prefixWord ++ tailWord_3924828).sum := by decide
  have hdescent : baseEnd_3924828 < baseStart_3924828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924874 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3924874 : Nat := 118140960795 + 3924874 * 2 ^ 59
def prefixEnd_3924874 : Nat := 4983230072969 + 3 ^ 40 * 3924874 * 2
def baseEnd_3924874 : Nat := 2015346870334782146124839

theorem tailTrace_3924874 : CollatzResearch.WordTrace tailWord_3924874 prefixEnd_3924874 2015346870334782146124839 := by
  unfold tailWord_3924874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35787978795714821989449419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95434610121906191971865117 35787978795714821989449419)
  ·
    refine ⟨53681968193572232984174129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35787978795714821989449419 53681968193572232984174129)
    ·
      refine ⟨40261476145179174738130597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53681968193572232984174129 40261476145179174738130597)
      ·
        refine ⟨7549026777221095263399487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40261476145179174738130597 7549026777221095263399487)
        ·
          refine ⟨11323540165831642895099231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7549026777221095263399487 11323540165831642895099231)
          ·
            refine ⟨16985310248747464342648847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11323540165831642895099231 16985310248747464342648847)
            ·
              refine ⟨25477965373121196513973271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16985310248747464342648847 25477965373121196513973271)
              ·
                refine ⟨38216948059681794770959907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25477965373121196513973271 38216948059681794770959907)
                ·
                  refine ⟨57325422089522692156439861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38216948059681794770959907 57325422089522692156439861)
                  ·
                    refine ⟨5374258320892752389666237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57325422089522692156439861 5374258320892752389666237)
                    ·
                      refine ⟨2015346870334782146124839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5374258320892752389666237 2015346870334782146124839)
                      ·
                        rfl

theorem cell23_3924874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3924874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924874 prefixEnd_3924874 := by exact prefixLift 3924874
  have htrace : WordTrace (prefixWord ++ tailWord_3924874) baseStart_3924874 baseEnd_3924874 := by
    simpa [prefixWord, tailWord_3924874, baseEnd_3924874] using wordTrace_append hprefix tailTrace_3924874
  have hstable : (prefixWord ++ tailWord_3924874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924874).length < 2 ^ (prefixWord ++ tailWord_3924874).sum := by decide
  have hdescent : baseEnd_3924874 < baseStart_3924874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924909 : List Nat := [1, 5, 2, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3924909 : Nat := 118140960795 + 3924909 * 2 ^ 59
def prefixEnd_3924909 : Nat := 4983230072969 + 3 ^ 40 * 3924909 * 2
def baseEnd_3924909 : Nat := 2015364842157689509187179

theorem tailTrace_3924909 : CollatzResearch.WordTrace tailWord_3924909 prefixEnd_3924909 2015364842157689509187179 := by
  unfold tailWord_3924909
  simp only [CollatzResearch.WordTrace]
  refine ⟨143153191737732488935321781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95435461158488325956881187 143153191737732488935321781)
  ·
    refine ⟨13420611725412420837686417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143153191737732488935321781 13420611725412420837686417)
    ·
      refine ⟨10065458794059315628264813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13420611725412420837686417 10065458794059315628264813)
      ·
        refine ⟨3774547047772243360599305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10065458794059315628264813 3774547047772243360599305)
        ·
          refine ⟨2830910285829182520449479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3774547047772243360599305 2830910285829182520449479)
          ·
            refine ⟨4246365428743773780674219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830910285829182520449479 4246365428743773780674219)
            ·
              refine ⟨6369548143115660671011329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246365428743773780674219 6369548143115660671011329)
              ·
                refine ⟨4777161107336745503258497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369548143115660671011329 4777161107336745503258497)
                ·
                  refine ⟨3582870830502559127443873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4777161107336745503258497 3582870830502559127443873)
                  ·
                    refine ⟨2687153122876919345582905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3582870830502559127443873 2687153122876919345582905)
                    ·
                      refine ⟨2015364842157689509187179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2687153122876919345582905 2015364842157689509187179)
                      ·
                        rfl

theorem cell23_3924909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3924909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924909 prefixEnd_3924909 := by exact prefixLift 3924909
  have htrace : WordTrace (prefixWord ++ tailWord_3924909) baseStart_3924909 baseEnd_3924909 := by
    simpa [prefixWord, tailWord_3924909, baseEnd_3924909] using wordTrace_append hprefix tailTrace_3924909
  have hstable : (prefixWord ++ tailWord_3924909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924909).length < 2 ^ (prefixWord ++ tailWord_3924909).sum := by decide
  have hdescent : baseEnd_3924909 < baseStart_3924909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3924987 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4]
def baseStart_3924987 : Nat := 118140960795 + 3924987 * 2 ^ 59
def prefixEnd_3924987 : Nat := 4983230072969 + 3 ^ 40 * 3924987 * 2
def baseEnd_3924987 : Nat := 2015404893648740204011819

theorem tailTrace_3924987 : CollatzResearch.WordTrace tailWord_3924987 prefixEnd_3924987 2015404893648740204011819 := by
  unfold tailWord_3924987
  simp only [CollatzResearch.WordTrace]
  refine ⟨143156036631449908256661215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95437357754299938837774143 143156036631449908256661215)
  ·
    refine ⟨214734054947174862384991823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143156036631449908256661215 214734054947174862384991823)
    ·
      refine ⟨322101082420762293577487735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214734054947174862384991823 322101082420762293577487735)
      ·
        refine ⟨483151623631143440366231603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322101082420762293577487735 483151623631143440366231603)
        ·
          refine ⟨724727435446715160549347405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483151623631143440366231603 724727435446715160549347405)
          ·
            refine ⟨271772788292518185206005277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724727435446715160549347405 271772788292518185206005277)
            ·
              refine ⟨101914795609694319452251979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271772788292518185206005277 101914795609694319452251979)
              ·
                refine ⟨152872193414541479178377969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101914795609694319452251979 152872193414541479178377969)
                ·
                  refine ⟨114654145060906109383783477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152872193414541479178377969 114654145060906109383783477)
                  ·
                    refine ⟨10748826099459947754729701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114654145060906109383783477 10748826099459947754729701)
                    ·
                      refine ⟨2015404893648740204011819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10748826099459947754729701 2015404893648740204011819)
                      ·
                        rfl

theorem cell23_3924987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_3924987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3924987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3924987 prefixEnd_3924987 := by exact prefixLift 3924987
  have htrace : WordTrace (prefixWord ++ tailWord_3924987) baseStart_3924987 baseEnd_3924987 := by
    simpa [prefixWord, tailWord_3924987, baseEnd_3924987] using wordTrace_append hprefix tailTrace_3924987
  have hstable : (prefixWord ++ tailWord_3924987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3924987).length < 2 ^ (prefixWord ++ tailWord_3924987).sum := by decide
  have hdescent : baseEnd_3924987 < baseStart_3924987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3924987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925027 : List Nat := [1, 1, 1, 4, 3, 13]
def baseStart_3925027 : Nat := 118140960795 + 3925027 * 2 ^ 59
def prefixEnd_3925027 : Nat := 4983230072969 + 3 ^ 40 * 3925027 * 2
def baseEnd_3925027 : Nat := 8293931822530535174945

theorem tailTrace_3925027 : CollatzResearch.WordTrace tailWord_3925027 prefixEnd_3925027 8293931822530535174945 := by
  unfold tailWord_3925027
  simp only [CollatzResearch.WordTrace]
  refine ⟨143157495551304995088117335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95438330367536663392078223 143157495551304995088117335)
  ·
    refine ⟨214736243326957492632176003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143157495551304995088117335 214736243326957492632176003)
    ·
      refine ⟨322104364990436238948264005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214736243326957492632176003 322104364990436238948264005)
      ·
        refine ⟨60394568435706794802799501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322104364990436238948264005 60394568435706794802799501)
        ·
          refine ⟨22647963163390048051049813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60394568435706794802799501 22647963163390048051049813)
          ·
            refine ⟨8293931822530535174945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 22647963163390048051049813 8293931822530535174945)
            ·
              rfl

theorem cell23_3925027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 13].length) (baseStart_3925027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925027 prefixEnd_3925027 := by exact prefixLift 3925027
  have htrace : WordTrace (prefixWord ++ tailWord_3925027) baseStart_3925027 baseEnd_3925027 := by
    simpa [prefixWord, tailWord_3925027, baseEnd_3925027] using wordTrace_append hprefix tailTrace_3925027
  have hstable : (prefixWord ++ tailWord_3925027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925027).length < 2 ^ (prefixWord ++ tailWord_3925027).sum := by decide
  have hdescent : baseEnd_3925027 < baseStart_3925027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925078 : List Nat := [5, 2, 2, 1, 2, 1, 10]
def baseStart_3925078 : Nat := 118140960795 + 3925078 * 2 ^ 59
def prefixEnd_3925078 : Nat := 4983230072969 + 3 ^ 40 * 3925078 * 2
def baseEnd_3925078 : Nat := 24882118770225917876221

theorem tailTrace_3925078 : CollatzResearch.WordTrace tailWord_3925078 prefixEnd_3925078 24882118770225917876221 := by
  unfold tailWord_3925078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947459729632514424888993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95439570449413487198815925 8947459729632514424888993)
  ·
    refine ⟨6710594797224385818666745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8947459729632514424888993 6710594797224385818666745)
    ·
      refine ⟨5032946097918289364000059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6710594797224385818666745 5032946097918289364000059)
      ·
        refine ⟨7549419146877434046000089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032946097918289364000059 7549419146877434046000089)
        ·
          refine ⟨5662064360158075534500067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7549419146877434046000089 5662064360158075534500067)
          ·
            refine ⟨8493096540237113301750101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662064360158075534500067 8493096540237113301750101)
            ·
              refine ⟨24882118770225917876221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8493096540237113301750101 24882118770225917876221)
              ·
                rfl

theorem cell23_3925078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 10].length) (baseStart_3925078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925078 prefixEnd_3925078 := by exact prefixLift 3925078
  have htrace : WordTrace (prefixWord ++ tailWord_3925078) baseStart_3925078 baseEnd_3925078 := by
    simpa [prefixWord, tailWord_3925078, baseEnd_3925078] using wordTrace_append hprefix tailTrace_3925078
  have hstable : (prefixWord ++ tailWord_3925078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925078).length < 2 ^ (prefixWord ++ tailWord_3925078).sum := by decide
  have hdescent : baseEnd_3925078 < baseStart_3925078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925081 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 5, 3, 2]
def baseStart_3925081 : Nat := 118140960795 + 3925081 * 2 ^ 59
def prefixEnd_3925081 : Nat := 4983230072969 + 3 ^ 40 * 3925081 * 2
def baseEnd_3925081 : Nat := 2015453160830262836236387

theorem tailTrace_3925081 : CollatzResearch.WordTrace tailWord_3925081 prefixEnd_3925081 2015453160830262836236387 := by
  unfold tailWord_3925081
  simp only [CollatzResearch.WordTrace]
  refine ⟨143159465093109362310583097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95439643395406241540388731 143159465093109362310583097)
  ·
    refine ⟨107369598819832021732937323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143159465093109362310583097 107369598819832021732937323)
    ·
      refine ⟨161054398229748032599405985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107369598819832021732937323 161054398229748032599405985)
      ·
        refine ⟨120790798672311024449554489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161054398229748032599405985 120790798672311024449554489)
        ·
          refine ⟨90593099004233268337165867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120790798672311024449554489 90593099004233268337165867)
          ·
            refine ⟨135889648506349902505748801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90593099004233268337165867 135889648506349902505748801)
            ·
              refine ⟨101917236379762426879311601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135889648506349902505748801 101917236379762426879311601)
              ·
                refine ⟨76437927284821820159483701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101917236379762426879311601 76437927284821820159483701)
                ·
                  refine ⟨7166055682952045639951597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76437927284821820159483701 7166055682952045639951597)
                  ·
                    refine ⟨2687270881107017114981849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7166055682952045639951597 2687270881107017114981849)
                    ·
                      refine ⟨2015453160830262836236387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2687270881107017114981849 2015453160830262836236387)
                      ·
                        rfl

theorem cell23_3925081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_3925081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925081 prefixEnd_3925081 := by exact prefixLift 3925081
  have htrace : WordTrace (prefixWord ++ tailWord_3925081) baseStart_3925081 baseEnd_3925081 := by
    simpa [prefixWord, tailWord_3925081, baseEnd_3925081] using wordTrace_append hprefix tailTrace_3925081
  have hstable : (prefixWord ++ tailWord_3925081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925081).length < 2 ^ (prefixWord ++ tailWord_3925081).sum := by decide
  have hdescent : baseEnd_3925081 < baseStart_3925081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925104 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 2, 6]
def baseStart_3925104 : Nat := 118140960795 + 3925104 * 2 ^ 59
def prefixEnd_3925104 : Nat := 4983230072969 + 3 ^ 40 * 3925104 * 2
def baseEnd_3925104 : Nat := 671821656961772082082927

theorem tailTrace_3925104 : CollatzResearch.WordTrace tailWord_3925104 prefixEnd_3925104 671821656961772082082927 := by
  unfold tailWord_3925104
  simp only [CollatzResearch.WordTrace]
  refine ⟨71580151986013018619335183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95440202648017358159113577 71580151986013018619335183)
  ·
    refine ⟨107370227979019527929002775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71580151986013018619335183 107370227979019527929002775)
    ·
      refine ⟨161055341968529291893504163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107370227979019527929002775 161055341968529291893504163)
      ·
        refine ⟨241583012952793937840256245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161055341968529291893504163 241583012952793937840256245)
        ·
          refine ⟨22648407464324431672524023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241583012952793937840256245 22648407464324431672524023)
          ·
            refine ⟨33972611196486647508786035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22648407464324431672524023 33972611196486647508786035)
            ·
              refine ⟨50958916794729971263179053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33972611196486647508786035 50958916794729971263179053)
              ·
                refine ⟨19109593798023739223692145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50958916794729971263179053 19109593798023739223692145)
                ·
                  refine ⟨14332195348517804417769109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19109593798023739223692145 14332195348517804417769109)
                  ·
                    refine ⟨671821656961772082082927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14332195348517804417769109 671821656961772082082927)
                    ·
                      rfl

theorem cell23_3925104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_3925104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925104 prefixEnd_3925104 := by exact prefixLift 3925104
  have htrace : WordTrace (prefixWord ++ tailWord_3925104) baseStart_3925104 baseEnd_3925104 := by
    simpa [prefixWord, tailWord_3925104, baseEnd_3925104] using wordTrace_append hprefix tailTrace_3925104
  have hstable : (prefixWord ++ tailWord_3925104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925104).length < 2 ^ (prefixWord ++ tailWord_3925104).sum := by decide
  have hdescent : baseEnd_3925104 < baseStart_3925104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925164 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 1, 7]
def baseStart_3925164 : Nat := 118140960795 + 3925164 * 2 ^ 59
def prefixEnd_3925164 : Nat := 4983230072969 + 3 ^ 40 * 3925164 * 2
def baseEnd_3925164 : Nat := 671831926574862003832835

theorem tailTrace_3925164 : CollatzResearch.WordTrace tailWord_3925164 prefixEnd_3925164 671831926574862003832835 := by
  unfold tailWord_3925164
  simp only [CollatzResearch.WordTrace]
  refine ⟨71581246175904333742927273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95441661567872444990569697 71581246175904333742927273)
  ·
    refine ⟨53685934631928250307195455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71581246175904333742927273 53685934631928250307195455)
    ·
      refine ⟨80528901947892375460793183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53685934631928250307195455 80528901947892375460793183)
      ·
        refine ⟨120793352921838563191189775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80528901947892375460793183 120793352921838563191189775)
        ·
          refine ⟨181190029382757844786784663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120793352921838563191189775 181190029382757844786784663)
          ·
            refine ⟨271785044074136767180176995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181190029382757844786784663 271785044074136767180176995)
            ·
              refine ⟨407677566111205150770265493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271785044074136767180176995 407677566111205150770265493)
              ·
                refine ⟨19109885911462741442356195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 407677566111205150770265493 19109885911462741442356195)
                ·
                  refine ⟨28664828867194112163534293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19109885911462741442356195 28664828867194112163534293)
                  ·
                    refine ⟨671831926574862003832835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28664828867194112163534293 671831926574862003832835)
                    ·
                      rfl

theorem cell23_3925164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_3925164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925164 prefixEnd_3925164 := by exact prefixLift 3925164
  have htrace : WordTrace (prefixWord ++ tailWord_3925164) baseStart_3925164 baseEnd_3925164 := by
    simpa [prefixWord, tailWord_3925164, baseEnd_3925164] using wordTrace_append hprefix tailTrace_3925164
  have hstable : (prefixWord ++ tailWord_3925164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925164).length < 2 ^ (prefixWord ++ tailWord_3925164).sum := by decide
  have hdescent : baseEnd_3925164 < baseStart_3925164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925181 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_3925181 : Nat := 118140960795 + 3925181 * 2 ^ 59
def prefixEnd_3925181 : Nat := 4983230072969 + 3 ^ 40 * 3925181 * 2
def baseEnd_3925181 : Nat := 671834836298570814995309

theorem tailTrace_3925181 : CollatzResearch.WordTrace tailWord_3925181 prefixEnd_3925181 671834836298570814995309 := by
  unfold tailWord_3925181
  simp only [CollatzResearch.WordTrace]
  refine ⟨143163112392747079389223397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95442074928498052926148931 143163112392747079389223397)
  ·
    refine ⟨26843083573640077385479387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143163112392747079389223397 26843083573640077385479387)
    ·
      refine ⟨40264625360460116078219081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26843083573640077385479387 40264625360460116078219081)
      ·
        refine ⟨30198469020345087058664311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40264625360460116078219081 30198469020345087058664311)
        ·
          refine ⟨45297703530517630587996467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30198469020345087058664311 45297703530517630587996467)
          ·
            refine ⟨67946555295776445881994701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45297703530517630587996467 67946555295776445881994701)
            ·
              refine ⟨25479958235916167205748013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67946555295776445881994701 25479958235916167205748013)
              ·
                refine ⟨9554984338468562702155505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25479958235916167205748013 9554984338468562702155505)
                ·
                  refine ⟨7166238253851422026616629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9554984338468562702155505 7166238253851422026616629)
                  ·
                    refine ⟨671834836298570814995309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7166238253851422026616629 671834836298570814995309)
                    ·
                      rfl

theorem cell23_3925181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_3925181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925181 prefixEnd_3925181 := by exact prefixLift 3925181
  have htrace : WordTrace (prefixWord ++ tailWord_3925181) baseStart_3925181 baseEnd_3925181 := by
    simpa [prefixWord, tailWord_3925181, baseEnd_3925181] using wordTrace_append hprefix tailTrace_3925181
  have hstable : (prefixWord ++ tailWord_3925181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925181).length < 2 ^ (prefixWord ++ tailWord_3925181).sum := by decide
  have hdescent : baseEnd_3925181 < baseStart_3925181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925228 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 3, 4]
def baseStart_3925228 : Nat := 118140960795 + 3925228 * 2 ^ 59
def prefixEnd_3925228 : Nat := 4983230072969 + 3 ^ 40 * 3925228 * 2
def baseEnd_3925228 : Nat := 671842880828824587032737

theorem tailTrace_3925228 : CollatzResearch.WordTrace tailWord_3925228 prefixEnd_3925228 671842880828824587032737 := by
  unfold tailWord_3925228
  simp only [CollatzResearch.WordTrace]
  refine ⟨71582413311788403208092169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95443217749051204277456225 71582413311788403208092169)
  ·
    refine ⟨53686809983841302406069127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71582413311788403208092169 53686809983841302406069127)
    ·
      refine ⟨80530214975761953609103691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53686809983841302406069127 80530214975761953609103691)
      ·
        refine ⟨120795322463642930413655537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80530214975761953609103691 120795322463642930413655537)
        ·
          refine ⟨90596491847732197810241653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120795322463642930413655537 90596491847732197810241653)
          ·
            refine ⟨8493421110724893544710155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90596491847732197810241653 8493421110724893544710155)
            ·
              refine ⟨12740131666087340317065233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8493421110724893544710155 12740131666087340317065233)
              ·
                refine ⟨9555098749565505237798925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12740131666087340317065233 9555098749565505237798925)
                ·
                  refine ⟨3583162031087064464174597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9555098749565505237798925 3583162031087064464174597)
                  ·
                    refine ⟨671842880828824587032737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3583162031087064464174597 671842880828824587032737)
                    ·
                      rfl

theorem cell23_3925228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_3925228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925228 prefixEnd_3925228 := by exact prefixLift 3925228
  have htrace : WordTrace (prefixWord ++ tailWord_3925228) baseStart_3925228 baseEnd_3925228 := by
    simpa [prefixWord, tailWord_3925228, baseEnd_3925228] using wordTrace_append hprefix tailTrace_3925228
  have hstable : (prefixWord ++ tailWord_3925228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925228).length < 2 ^ (prefixWord ++ tailWord_3925228).sum := by decide
  have hdescent : baseEnd_3925228 < baseStart_3925228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925285 : List Nat := [1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_3925285 : Nat := 118140960795 + 3925285 * 2 ^ 59
def prefixEnd_3925285 : Nat := 4983230072969 + 3 ^ 40 * 3925285 * 2
def baseEnd_3925285 : Nat := 2015557910883780038085449

theorem tailTrace_3925285 : CollatzResearch.WordTrace tailWord_3925285 prefixEnd_3925285 2015557910883780038085449 := by
  unfold tailWord_3925285
  simp only [CollatzResearch.WordTrace]
  refine ⟨143166905584370305151009309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95444603722913536767339539 143166905584370305151009309)
  ·
    refine ⟨53687589594138864431628491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143166905584370305151009309 53687589594138864431628491)
    ·
      refine ⟨80531384391208296647442737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53687589594138864431628491 80531384391208296647442737)
      ·
        refine ⟨60398538293406222485582053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80531384391208296647442737 60398538293406222485582053)
        ·
          refine ⟨11324725930013666716046635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60398538293406222485582053 11324725930013666716046635)
          ·
            refine ⟨16987088895020500074069953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11324725930013666716046635 16987088895020500074069953)
            ·
              refine ⟨12740316671265375055552465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16987088895020500074069953 12740316671265375055552465)
              ·
                refine ⟨9555237503449031291664349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12740316671265375055552465 9555237503449031291664349)
                ·
                  refine ⟨3583214063793386734374131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9555237503449031291664349 3583214063793386734374131)
                  ·
                    refine ⟨5374821095690080101561197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3583214063793386734374131 5374821095690080101561197)
                    ·
                      refine ⟨2015557910883780038085449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5374821095690080101561197 2015557910883780038085449)
                      ·
                        rfl

theorem cell23_3925285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_3925285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925285 prefixEnd_3925285 := by exact prefixLift 3925285
  have htrace : WordTrace (prefixWord ++ tailWord_3925285) baseStart_3925285 baseEnd_3925285 := by
    simpa [prefixWord, tailWord_3925285, baseEnd_3925285] using wordTrace_append hprefix tailTrace_3925285
  have hstable : (prefixWord ++ tailWord_3925285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925285).length < 2 ^ (prefixWord ++ tailWord_3925285).sum := by decide
  have hdescent : baseEnd_3925285 < baseStart_3925285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925319 : List Nat := [1, 1, 4, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_3925319 : Nat := 118140960795 + 3925319 * 2 ^ 59
def prefixEnd_3925319 : Nat := 4983230072969 + 3 ^ 40 * 3925319 * 2
def baseEnd_3925319 : Nat := 2015575369226032905060293

theorem tailTrace_3925319 : CollatzResearch.WordTrace tailWord_3925319 prefixEnd_3925319 2015575369226032905060293 := by
  unfold tailWord_3925319
  simp only [CollatzResearch.WordTrace]
  refine ⟨143168145666247128957747011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95445430444164752638498007 143168145666247128957747011)
  ·
    refine ⟨214752218499370693436620517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143168145666247128957747011 214752218499370693436620517)
    ·
      refine ⟨40266040968632005019366347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214752218499370693436620517 40266040968632005019366347)
      ·
        refine ⟨60399061452948007529049521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40266040968632005019366347 60399061452948007529049521)
        ·
          refine ⟨45299296089711005646787141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60399061452948007529049521 45299296089711005646787141)
          ·
            refine ⟨8493618016820813558772589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45299296089711005646787141 8493618016820813558772589)
            ·
              refine ⟨3185106756307805084539721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8493618016820813558772589 3185106756307805084539721)
              ·
                refine ⟨2388830067230853813404791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3185106756307805084539721 2388830067230853813404791)
                ·
                  refine ⟨3583245100846280720107187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388830067230853813404791 3583245100846280720107187)
                  ·
                    refine ⟨5374867651269421080160781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3583245100846280720107187 5374867651269421080160781)
                    ·
                      refine ⟨2015575369226032905060293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5374867651269421080160781 2015575369226032905060293)
                      ·
                        rfl

theorem cell23_3925319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_3925319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925319 prefixEnd_3925319 := by exact prefixLift 3925319
  have htrace : WordTrace (prefixWord ++ tailWord_3925319) baseStart_3925319 baseEnd_3925319 := by
    simpa [prefixWord, tailWord_3925319, baseEnd_3925319] using wordTrace_append hprefix tailTrace_3925319
  have hstable : (prefixWord ++ tailWord_3925319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925319).length < 2 ^ (prefixWord ++ tailWord_3925319).sum := by decide
  have hdescent : baseEnd_3925319 < baseStart_3925319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925321 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_3925321 : Nat := 118140960795 + 3925321 * 2 ^ 59
def prefixEnd_3925321 : Nat := 4983230072969 + 3 ^ 40 * 3925321 * 2
def baseEnd_3925321 : Nat := 2015576396187341897235283

theorem tailTrace_3925321 : CollatzResearch.WordTrace tailWord_3925321 prefixEnd_3925321 2015576396187341897235283 := by
  unfold tailWord_3925321
  simp only [CollatzResearch.WordTrace]
  refine ⟨143168218612239883299319817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95445479074826588866213211 143168218612239883299319817)
  ·
    refine ⟨107376163959179912474489863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143168218612239883299319817 107376163959179912474489863)
    ·
      refine ⟨161064245938769868711734795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107376163959179912474489863 161064245938769868711734795)
      ·
        refine ⟨241596368908154803067602193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161064245938769868711734795 241596368908154803067602193)
        ·
          refine ⟨181197276681116102300701645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241596368908154803067602193 181197276681116102300701645)
          ·
            refine ⟨67948978755418538362763117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181197276681116102300701645 67948978755418538362763117)
            ·
              refine ⟨25480867033281951886036169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67948978755418538362763117 25480867033281951886036169)
              ·
                refine ⟨19110650274961463914527127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25480867033281951886036169 19110650274961463914527127)
                ·
                  refine ⟨28665975412442195871790691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19110650274961463914527127 28665975412442195871790691)
                  ·
                    refine ⟨42998963118663293807686037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28665975412442195871790691 42998963118663293807686037)
                    ·
                      refine ⟨2015576396187341897235283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42998963118663293807686037 2015576396187341897235283)
                      ·
                        rfl

theorem cell23_3925321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_3925321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925321 prefixEnd_3925321 := by exact prefixLift 3925321
  have htrace : WordTrace (prefixWord ++ tailWord_3925321) baseStart_3925321 baseEnd_3925321 := by
    simpa [prefixWord, tailWord_3925321, baseEnd_3925321] using wordTrace_append hprefix tailTrace_3925321
  have hstable : (prefixWord ++ tailWord_3925321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925321).length < 2 ^ (prefixWord ++ tailWord_3925321).sum := by decide
  have hdescent : baseEnd_3925321 < baseStart_3925321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925328 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3]
def baseStart_3925328 : Nat := 118140960795 + 3925328 * 2 ^ 59
def prefixEnd_3925328 : Nat := 4983230072969 + 3 ^ 40 * 3925328 * 2
def baseEnd_3925328 : Nat := 2015579990551923369847751

theorem tailTrace_3925328 : CollatzResearch.WordTrace tailWord_3925328 prefixEnd_3925328 2015579990551923369847751 := by
  unfold tailWord_3925328
  simp only [CollatzResearch.WordTrace]
  refine ⟨71584236961607261747412319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95445649282143015663216425 71584236961607261747412319)
  ·
    refine ⟨107376355442410892621118479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71584236961607261747412319 107376355442410892621118479)
    ·
      refine ⟨161064533163616338931677719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107376355442410892621118479 161064533163616338931677719)
      ·
        refine ⟨241596799745424508397516579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161064533163616338931677719 241596799745424508397516579)
        ·
          refine ⟨362395199618136762596274869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241596799745424508397516579 362395199618136762596274869)
          ·
            refine ⟨33974549964200321493400769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362395199618136762596274869 33974549964200321493400769)
            ·
              refine ⟨25480912473150241120050577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33974549964200321493400769 25480912473150241120050577)
              ·
                refine ⟨19110684354862680840037933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25480912473150241120050577 19110684354862680840037933)
                ·
                  refine ⟨7166506633073505315014225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19110684354862680840037933 7166506633073505315014225)
                  ·
                    refine ⟨5374879974805128986260669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7166506633073505315014225 5374879974805128986260669)
                    ·
                      refine ⟨2015579990551923369847751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5374879974805128986260669 2015579990551923369847751)
                      ·
                        rfl

theorem cell23_3925328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_3925328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925328 prefixEnd_3925328 := by exact prefixLift 3925328
  have htrace : WordTrace (prefixWord ++ tailWord_3925328) baseStart_3925328 baseEnd_3925328 := by
    simpa [prefixWord, tailWord_3925328, baseEnd_3925328] using wordTrace_append hprefix tailTrace_3925328
  have hstable : (prefixWord ++ tailWord_3925328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925328).length < 2 ^ (prefixWord ++ tailWord_3925328).sum := by decide
  have hdescent : baseEnd_3925328 < baseStart_3925328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925331 : List Nat := [1, 1, 1, 2, 1, 1, 8, 8]
def baseStart_3925331 : Nat := 118140960795 + 3925331 * 2 ^ 59
def prefixEnd_3925331 : Nat := 4983230072969 + 3 ^ 40 * 3925331 * 2
def baseEnd_3925331 : Nat := 74651167814588402152231

theorem tailTrace_3925331 : CollatzResearch.WordTrace tailWord_3925331 prefixEnd_3925331 74651167814588402152231 := by
  unfold tailWord_3925331
  simp only [CollatzResearch.WordTrace]
  refine ⟨143168583342203655007183847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95445722228135770004789231 143168583342203655007183847)
  ·
    refine ⟨214752875013305482510775771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143168583342203655007183847 214752875013305482510775771)
    ·
      refine ⟨322129312519958223766163657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214752875013305482510775771 322129312519958223766163657)
      ·
        refine ⟨241596984389968667824622743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322129312519958223766163657 241596984389968667824622743)
        ·
          refine ⟨362395476584953001736934115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241596984389968667824622743 362395476584953001736934115)
          ·
            refine ⟨543593214877429502605401173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362395476584953001736934115 543593214877429502605401173)
            ·
              refine ⟨6370232986844876983657045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 543593214877429502605401173 6370232986844876983657045)
              ·
                refine ⟨74651167814588402152231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6370232986844876983657045 74651167814588402152231)
                ·
                  rfl

theorem cell23_3925331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 8].length) (baseStart_3925331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925331 prefixEnd_3925331 := by exact prefixLift 3925331
  have htrace : WordTrace (prefixWord ++ tailWord_3925331) baseStart_3925331 baseEnd_3925331 := by
    simpa [prefixWord, tailWord_3925331, baseEnd_3925331] using wordTrace_append hprefix tailTrace_3925331
  have hstable : (prefixWord ++ tailWord_3925331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925331).length < 2 ^ (prefixWord ++ tailWord_3925331).sum := by decide
  have hdescent : baseEnd_3925331 < baseStart_3925331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3925335 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 2, 4]
def baseStart_3925335 : Nat := 118140960795 + 3925335 * 2 ^ 59
def prefixEnd_3925335 : Nat := 4983230072969 + 3 ^ 40 * 3925335 * 2
def baseEnd_3925335 : Nat := 671861194972168280820073

theorem tailTrace_3925335 : CollatzResearch.WordTrace tailWord_3925335 prefixEnd_3925335 671861194972168280820073 := by
  unfold tailWord_3925335
  simp only [CollatzResearch.WordTrace]
  refine ⟨143168729234189163690329459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95445819489459442460219639 143168729234189163690329459)
  ·
    refine ⟨214753093851283745535494189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143168729234189163690329459 214753093851283745535494189)
    ·
      refine ⟨80532410194231404575810321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214753093851283745535494189 80532410194231404575810321)
      ·
        refine ⟨60399307645673553431857741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80532410194231404575810321 60399307645673553431857741)
        ·
          refine ⟨22649740367127582536946653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60399307645673553431857741 22649740367127582536946653)
          ·
            refine ⟨8493652637672843451354995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22649740367127582536946653 8493652637672843451354995)
            ·
              refine ⟨12740478956509265177032493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8493652637672843451354995 12740478956509265177032493)
              ·
                refine ⟨4777679608690974441387185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12740478956509265177032493 4777679608690974441387185)
                ·
                  refine ⟨3583259706518230831040389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4777679608690974441387185 3583259706518230831040389)
                  ·
                    refine ⟨671861194972168280820073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3583259706518230831040389 671861194972168280820073)
                    ·
                      rfl

theorem cell23_3925335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_3925335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3925335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3925335 prefixEnd_3925335 := by exact prefixLift 3925335
  have htrace : WordTrace (prefixWord ++ tailWord_3925335) baseStart_3925335 baseEnd_3925335 := by
    simpa [prefixWord, tailWord_3925335, baseEnd_3925335] using wordTrace_append hprefix tailTrace_3925335
  have hstable : (prefixWord ++ tailWord_3925335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3925335).length < 2 ^ (prefixWord ++ tailWord_3925335).sum := by decide
  have hdescent : baseEnd_3925335 < baseStart_3925335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3925335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
