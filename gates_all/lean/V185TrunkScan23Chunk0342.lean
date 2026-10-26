import V185TrunkScan23Chunk0341

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2021893 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_2021893 : Nat := 118140960795 + 2021893 * 2 ^ 59
def prefixEnd_2021893 : Nat := 4983230072969 + 3 ^ 40 * 2021893 * 2
def baseEnd_2021893 : Nat := 1038202940961163068038989

theorem tailTrace_2021893 : CollatzResearch.WordTrace tailWord_2021893 prefixEnd_2021893 1038202940961163068038989 := by
  unfold tailWord_2021893
  simp only [CollatzResearch.WordTrace]
  refine ⟨73744496064034447677830333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49162997376022965118553555 73744496064034447677830333)
  ·
    refine ⟨27654186024012917879186375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73744496064034447677830333 27654186024012917879186375)
    ·
      refine ⟨41481279036019376818779563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27654186024012917879186375 41481279036019376818779563)
      ·
        refine ⟨62221918554029065228169345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41481279036019376818779563 62221918554029065228169345)
        ·
          refine ⟨46666438915521798921127009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62221918554029065228169345 46666438915521798921127009)
          ·
            refine ⟨34999829186641349190845257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46666438915521798921127009 34999829186641349190845257)
            ·
              refine ⟨26249871889981011893133943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34999829186641349190845257 26249871889981011893133943)
              ·
                refine ⟨39374807834971517839700915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26249871889981011893133943 39374807834971517839700915)
                ·
                  refine ⟨59062211752457276759551373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39374807834971517839700915 59062211752457276759551373)
                  ·
                    refine ⟨22148329407171478784831765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59062211752457276759551373 22148329407171478784831765)
                    ·
                      refine ⟨1038202940961163068038989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22148329407171478784831765 1038202940961163068038989)
                      ·
                        rfl

theorem cell23_2021893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_2021893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021893 prefixEnd_2021893 := by exact prefixLift 2021893
  have htrace : WordTrace (prefixWord ++ tailWord_2021893) baseStart_2021893 baseEnd_2021893 := by
    simpa [prefixWord, tailWord_2021893, baseEnd_2021893] using wordTrace_append hprefix tailTrace_2021893
  have hstable : (prefixWord ++ tailWord_2021893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021893).length < 2 ^ (prefixWord ++ tailWord_2021893).sum := by decide
  have hdescent : baseEnd_2021893 < baseStart_2021893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021958 : List Nat := [6, 1, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_2021958 : Nat := 118140960795 + 2021958 * 2 ^ 59
def prefixEnd_2021958 : Nat := 4983230072969 + 3 ^ 40 * 2021958 * 2
def baseEnd_2021958 : Nat := 346078772401235104575397

theorem tailTrace_2021958 : CollatzResearch.WordTrace tailWord_2021958 prefixEnd_2021958 346078772401235104575397 := by
  unfold tailWord_2021958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304589587774967618092079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49164577872532642519297685 2304589587774967618092079)
  ·
    refine ⟨3456884381662451427138119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2304589587774967618092079 3456884381662451427138119)
    ·
      refine ⟨5185326572493677140707179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3456884381662451427138119 5185326572493677140707179)
      ·
        refine ⟨7777989858740515711060769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185326572493677140707179 7777989858740515711060769)
        ·
          refine ⟨5833492394055386783295577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7777989858740515711060769 5833492394055386783295577)
          ·
            refine ⟨4375119295541540087471683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5833492394055386783295577 4375119295541540087471683)
            ·
              refine ⟨6562678943312310131207525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375119295541540087471683 6562678943312310131207525)
              ·
                refine ⟨1230502301871058149601411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6562678943312310131207525 1230502301871058149601411)
                ·
                  refine ⟨1845753452806587224402117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230502301871058149601411 1845753452806587224402117)
                  ·
                    refine ⟨346078772401235104575397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1845753452806587224402117 346078772401235104575397)
                    ·
                      rfl

theorem cell23_2021958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_2021958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021958 prefixEnd_2021958 := by exact prefixLift 2021958
  have htrace : WordTrace (prefixWord ++ tailWord_2021958) baseStart_2021958 baseEnd_2021958 := by
    simpa [prefixWord, tailWord_2021958, baseEnd_2021958] using wordTrace_append hprefix tailTrace_2021958
  have hstable : (prefixWord ++ tailWord_2021958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021958).length < 2 ^ (prefixWord ++ tailWord_2021958).sum := by decide
  have hdescent : baseEnd_2021958 < baseStart_2021958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021987 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 4]
def baseStart_2021987 : Nat := 118140960795 + 2021987 * 2 ^ 59
def prefixEnd_2021987 : Nat := 4983230072969 + 3 ^ 40 * 2021987 * 2
def baseEnd_2021987 : Nat := 1038251208142685700263557

theorem tailTrace_2021987 : CollatzResearch.WordTrace tailWord_2021987 prefixEnd_2021987 1038251208142685700263557 := by
  unfold tailWord_2021987
  simp only [CollatzResearch.WordTrace]
  refine ⟨73747924525693901731752215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49165283017129267821168143 73747924525693901731752215)
  ·
    refine ⟨110621886788540852597628323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73747924525693901731752215 110621886788540852597628323)
    ·
      refine ⟨165932830182811278896442485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110621886788540852597628323 165932830182811278896442485)
      ·
        refine ⟨15556202829638557396541483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165932830182811278896442485 15556202829638557396541483)
        ·
          refine ⟨23334304244457836094812225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556202829638557396541483 23334304244457836094812225)
          ·
            refine ⟨17500728183343377071109169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23334304244457836094812225 17500728183343377071109169)
            ·
              refine ⟨13125546137507532803331877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17500728183343377071109169 13125546137507532803331877)
              ·
                refine ⟨2461039900782662400624727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13125546137507532803331877 2461039900782662400624727)
                ·
                  refine ⟨3691559851173993600937091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461039900782662400624727 3691559851173993600937091)
                  ·
                    refine ⟨5537339776760990401405637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3691559851173993600937091 5537339776760990401405637)
                    ·
                      refine ⟨1038251208142685700263557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5537339776760990401405637 1038251208142685700263557)
                      ·
                        rfl

theorem cell23_2021987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_2021987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021987 prefixEnd_2021987 := by exact prefixLift 2021987
  have htrace : WordTrace (prefixWord ++ tailWord_2021987) baseStart_2021987 baseEnd_2021987 := by
    simpa [prefixWord, tailWord_2021987, baseEnd_2021987] using wordTrace_append hprefix tailTrace_2021987
  have hstable : (prefixWord ++ tailWord_2021987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021987).length < 2 ^ (prefixWord ++ tailWord_2021987).sum := by decide
  have hdescent : baseEnd_2021987 < baseStart_2021987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021997 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2021997 : Nat := 118140960795 + 2021997 * 2 ^ 59
def prefixEnd_2021997 : Nat := 4983230072969 + 3 ^ 40 * 2021997 * 2
def baseEnd_2021997 : Nat := 346085447649743553712837

theorem tailTrace_2021997 : CollatzResearch.WordTrace tailWord_2021997 prefixEnd_2021997 346085447649743553712837 := by
  unfold tailWord_2021997
  simp only [CollatzResearch.WordTrace]
  refine ⟨73748289255657673439616245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49165526170438448959744163 73748289255657673439616245)
  ·
    refine ⟨6913902117717906884964023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73748289255657673439616245 6913902117717906884964023)
    ·
      refine ⟨10370853176576860327446035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6913902117717906884964023 10370853176576860327446035)
      ·
        refine ⟨15556279764865290491169053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10370853176576860327446035 15556279764865290491169053)
        ·
          refine ⟨5833604911824483934188395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15556279764865290491169053 5833604911824483934188395)
          ·
            refine ⟨8750407367736725901282593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833604911824483934188395 8750407367736725901282593)
            ·
              refine ⟨6562805525802544425961945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8750407367736725901282593 6562805525802544425961945)
              ·
                refine ⟨4922104144351908319471459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6562805525802544425961945 4922104144351908319471459)
                ·
                  refine ⟨7383156216527862479207189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922104144351908319471459 7383156216527862479207189)
                  ·
                    refine ⟨346085447649743553712837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7383156216527862479207189 346085447649743553712837)
                    ·
                      rfl

theorem cell23_2021997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2021997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021997 prefixEnd_2021997 := by exact prefixLift 2021997
  have htrace : WordTrace (prefixWord ++ tailWord_2021997) baseStart_2021997 baseEnd_2021997 := by
    simpa [prefixWord, tailWord_2021997, baseEnd_2021997] using wordTrace_append hprefix tailTrace_2021997
  have hstable : (prefixWord ++ tailWord_2021997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021997).length < 2 ^ (prefixWord ++ tailWord_2021997).sum := by decide
  have hdescent : baseEnd_2021997 < baseStart_2021997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021998 : List Nat := [4, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_2021998 : Nat := 118140960795 + 2021998 * 2 ^ 59
def prefixEnd_2021998 : Nat := 4983230072969 + 3 ^ 40 * 2021998 * 2
def baseEnd_2021998 : Nat := 1038256856429885157226007

theorem tailTrace_2021998 : CollatzResearch.WordTrace tailWord_2021998 prefixEnd_2021998 1038256856429885157226007 := by
  unfold tailWord_2021998
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218540716081756326300331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49165550485769367073601765 9218540716081756326300331)
  ·
    refine ⟨13827811074122634489450497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218540716081756326300331 13827811074122634489450497)
    ·
      refine ⟨10370858305591975867087873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13827811074122634489450497 10370858305591975867087873)
      ·
        refine ⟨7778143729193981900315905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10370858305591975867087873 7778143729193981900315905)
        ·
          refine ⟨5833607796895486425236929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7778143729193981900315905 5833607796895486425236929)
          ·
            refine ⟨4375205847671614818927697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5833607796895486425236929 4375205847671614818927697)
            ·
              refine ⟨3281404385753711114195773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375205847671614818927697 3281404385753711114195773)
              ·
                refine ⟨1230526644657641667823415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3281404385753711114195773 1230526644657641667823415)
                ·
                  refine ⟨1845789966986462501735123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230526644657641667823415 1845789966986462501735123)
                  ·
                    refine ⟨2768684950479693752602685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1845789966986462501735123 2768684950479693752602685)
                    ·
                      refine ⟨1038256856429885157226007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2768684950479693752602685 1038256856429885157226007)
                      ·
                        rfl

theorem cell23_2021998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_2021998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2021998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2021998 prefixEnd_2021998 := by exact prefixLift 2021998
  have htrace : WordTrace (prefixWord ++ tailWord_2021998) baseStart_2021998 baseEnd_2021998 := by
    simpa [prefixWord, tailWord_2021998, baseEnd_2021998] using wordTrace_append hprefix tailTrace_2021998
  have hstable : (prefixWord ++ tailWord_2021998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021998).length < 2 ^ (prefixWord ++ tailWord_2021998).sum := by decide
  have hdescent : baseEnd_2021998 < baseStart_2021998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022021 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 3, 2, 2]
def baseStart_2022021 : Nat := 118140960795 + 2022021 * 2 ^ 59
def prefixEnd_2022021 : Nat := 4983230072969 + 3 ^ 40 * 2022021 * 2
def baseEnd_2022021 : Nat := 1038268666484938567238401

theorem tailTrace_2022021 : CollatzResearch.WordTrace tailWord_2022021 prefixEnd_2022021 1038268666484938567238401 := by
  unfold tailWord_2022021
  simp only [CollatzResearch.WordTrace]
  refine ⟨73749164607570725538489917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49166109738380483692326611 73749164607570725538489917)
  ·
    refine ⟨27655936727839022076933719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73749164607570725538489917 27655936727839022076933719)
    ·
      refine ⟨41483905091758533115400579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27655936727839022076933719 41483905091758533115400579)
      ·
        refine ⟨62225857637637799673100869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41483905091758533115400579 62225857637637799673100869)
        ·
          refine ⟨11667348307057087438706413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62225857637637799673100869 11667348307057087438706413)
          ·
            refine ⟨4375255615146407789514905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11667348307057087438706413 4375255615146407789514905)
            ·
              refine ⟨3281441711359805842136179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375255615146407789514905 3281441711359805842136179)
              ·
                refine ⟨4922162567039708763204269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281441711359805842136179 4922162567039708763204269)
                ·
                  refine ⟨1845810962639890786201601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4922162567039708763204269 1845810962639890786201601)
                  ·
                    refine ⟨1384358221979918089651201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1845810962639890786201601 1384358221979918089651201)
                    ·
                      refine ⟨1038268666484938567238401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384358221979918089651201 1038268666484938567238401)
                      ·
                        rfl

theorem cell23_2022021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_2022021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022021 prefixEnd_2022021 := by exact prefixLift 2022021
  have htrace : WordTrace (prefixWord ++ tailWord_2022021) baseStart_2022021 baseEnd_2022021 := by
    simpa [prefixWord, tailWord_2022021, baseEnd_2022021] using wordTrace_append hprefix tailTrace_2022021
  have hstable : (prefixWord ++ tailWord_2022021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022021).length < 2 ^ (prefixWord ++ tailWord_2022021).sum := by decide
  have hdescent : baseEnd_2022021 < baseStart_2022021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022034 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2022034 : Nat := 118140960795 + 2022034 * 2 ^ 59
def prefixEnd_2022034 : Nat := 4983230072969 + 3 ^ 40 * 2022034 * 2
def baseEnd_2022034 : Nat := 1038275341733447016375841

theorem tailTrace_2022034 : CollatzResearch.WordTrace tailWord_2022034 prefixEnd_2022034 1038275341733447016375841 := by
  unfold tailWord_2022034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18437409689130907189678289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49166425837682419172475437 18437409689130907189678289)
  ·
    refine ⟨13828057266848180392258717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18437409689130907189678289 13828057266848180392258717)
    ·
      refine ⟨5185521475068067647097019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13828057266848180392258717 5185521475068067647097019)
      ·
        refine ⟨7778282212602101470645529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185521475068067647097019 7778282212602101470645529)
        ·
          refine ⟨5833711659451576102984147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7778282212602101470645529 5833711659451576102984147)
          ·
            refine ⟨8750567489177364154476221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833711659451576102984147 8750567489177364154476221)
            ·
              refine ⟨3281462808441511557928583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8750567489177364154476221 3281462808441511557928583)
              ·
                refine ⟨4922194212662267336892875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281462808441511557928583 4922194212662267336892875)
                ·
                  refine ⟨7383291318993401005339313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4922194212662267336892875 7383291318993401005339313)
                  ·
                    refine ⟨5537468489245050754004485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7383291318993401005339313 5537468489245050754004485)
                    ·
                      refine ⟨1038275341733447016375841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5537468489245050754004485 1038275341733447016375841)
                      ·
                        rfl

theorem cell23_2022034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2022034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022034 prefixEnd_2022034 := by exact prefixLift 2022034
  have htrace : WordTrace (prefixWord ++ tailWord_2022034) baseStart_2022034 baseEnd_2022034 := by
    simpa [prefixWord, tailWord_2022034, baseEnd_2022034] using wordTrace_append hprefix tailTrace_2022034
  have hstable : (prefixWord ++ tailWord_2022034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022034).length < 2 ^ (prefixWord ++ tailWord_2022034).sum := by decide
  have hdescent : baseEnd_2022034 < baseStart_2022034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022044 : List Nat := [2, 2, 3, 2, 2, 3, 2, 7]
def baseStart_2022044 : Nat := 118140960795 + 2022044 * 2 ^ 59
def prefixEnd_2022044 : Nat := 4983230072969 + 3 ^ 40 * 2022044 * 2
def baseEnd_2022044 : Nat := 38454832464444147305585

theorem tailTrace_2022044 : CollatzResearch.WordTrace tailWord_2022044 prefixEnd_2022044 38454832464444147305585 := by
  unfold tailWord_2022044
  simp only [CollatzResearch.WordTrace]
  refine ⟨36875001743243700233288593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49166668990991600311051457 36875001743243700233288593)
  ·
    refine ⟨27656251307432775174966445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36875001743243700233288593 27656251307432775174966445)
    ·
      refine ⟨10371094240287290690612417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27656251307432775174966445 10371094240287290690612417)
      ·
        refine ⟨7778320680215468017959313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10371094240287290690612417 7778320680215468017959313)
        ·
          refine ⟨5833740510161601013469485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7778320680215468017959313 5833740510161601013469485)
          ·
            refine ⟨2187652691310600380051057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5833740510161601013469485 2187652691310600380051057)
            ·
              refine ⟨1640739518482950285038293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187652691310600380051057 1640739518482950285038293)
              ·
                refine ⟨38454832464444147305585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1640739518482950285038293 38454832464444147305585)
                ·
                  rfl

theorem cell23_2022044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 7].length) (baseStart_2022044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022044 prefixEnd_2022044 := by exact prefixLift 2022044
  have htrace : WordTrace (prefixWord ++ tailWord_2022044) baseStart_2022044 baseEnd_2022044 := by
    simpa [prefixWord, tailWord_2022044, baseEnd_2022044] using wordTrace_append hprefix tailTrace_2022044
  have hstable : (prefixWord ++ tailWord_2022044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022044).length < 2 ^ (prefixWord ++ tailWord_2022044).sum := by decide
  have hdescent : baseEnd_2022044 < baseStart_2022044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022088 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 2, 1, 3]
def baseStart_2022088 : Nat := 118140960795 + 2022088 * 2 ^ 59
def prefixEnd_2022088 : Nat := 4983230072969 + 3 ^ 40 * 2022088 * 2
def baseEnd_2022088 : Nat := 1038303069688789805100593

theorem tailTrace_2022088 : CollatzResearch.WordTrace tailWord_2022088 prefixEnd_2022088 1038303069688789805100593 := by
  unfold tailWord_2022088
  simp only [CollatzResearch.WordTrace]
  refine ⟨36875804149163997990589459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49167738865551997320785945 36875804149163997990589459)
  ·
    refine ⟨55313706223745996985884189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36875804149163997990589459 55313706223745996985884189)
    ·
      refine ⟨20742639833904748869706571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55313706223745996985884189 20742639833904748869706571)
      ·
        refine ⟨31113959750857123304559857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20742639833904748869706571 31113959750857123304559857)
        ·
          refine ⟨23335469813142842478419893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31113959750857123304559857 23335469813142842478419893)
          ·
            refine ⟨2187700294982141482351865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23335469813142842478419893 2187700294982141482351865)
            ·
              refine ⟨1640775221236606111763899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187700294982141482351865 1640775221236606111763899)
              ·
                refine ⟨2461162831854909167645849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640775221236606111763899 2461162831854909167645849)
                ·
                  refine ⟨1845872123891181875734387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2461162831854909167645849 1845872123891181875734387)
                  ·
                    refine ⟨2768808185836772813601581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1845872123891181875734387 2768808185836772813601581)
                    ·
                      refine ⟨1038303069688789805100593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2768808185836772813601581 1038303069688789805100593)
                      ·
                        rfl

theorem cell23_2022088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_2022088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022088 prefixEnd_2022088 := by exact prefixLift 2022088
  have htrace : WordTrace (prefixWord ++ tailWord_2022088) baseStart_2022088 baseEnd_2022088 := by
    simpa [prefixWord, tailWord_2022088, baseEnd_2022088] using wordTrace_append hprefix tailTrace_2022088
  have hstable : (prefixWord ++ tailWord_2022088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022088).length < 2 ^ (prefixWord ++ tailWord_2022088).sum := by decide
  have hdescent : baseEnd_2022088 < baseStart_2022088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022154 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_2022154 : Nat := 118140960795 + 2022154 * 2 ^ 59
def prefixEnd_2022154 : Nat := 4983230072969 + 3 ^ 40 * 2022154 * 2
def baseEnd_2022154 : Nat := 1038336959411986546875289

theorem tailTrace_2022154 : CollatzResearch.WordTrace tailWord_2022154 prefixEnd_2022154 1038336959411986546875289 := by
  unfold tailWord_2022154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18438503879022222313270379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49169343677392592835387677 18438503879022222313270379)
  ·
    refine ⟨27657755818533333469905569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18438503879022222313270379 27657755818533333469905569)
    ·
      refine ⟨20743316863900000102429177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27657755818533333469905569 20743316863900000102429177)
      ·
        refine ⟨15557487647925000076821883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20743316863900000102429177 15557487647925000076821883)
        ·
          refine ⟨23336231471887500115232825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15557487647925000076821883 23336231471887500115232825)
          ·
            refine ⟨17502173603915625086424619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23336231471887500115232825 17502173603915625086424619)
            ·
              refine ⟨26253260405873437629636929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17502173603915625086424619 26253260405873437629636929)
              ·
                refine ⟨19689945304405078222227697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26253260405873437629636929 19689945304405078222227697)
                ·
                  refine ⟨14767458978303808666670773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19689945304405078222227697 14767458978303808666670773)
                  ·
                    refine ⟨1384449279215982062500385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14767458978303808666670773 1384449279215982062500385)
                    ·
                      refine ⟨1038336959411986546875289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384449279215982062500385 1038336959411986546875289)
                      ·
                        rfl

theorem cell23_2022154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_2022154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022154 prefixEnd_2022154 := by exact prefixLift 2022154
  have htrace : WordTrace (prefixWord ++ tailWord_2022154) baseStart_2022154 baseEnd_2022154 := by
    simpa [prefixWord, tailWord_2022154, baseEnd_2022154] using wordTrace_append hprefix tailTrace_2022154
  have hstable : (prefixWord ++ tailWord_2022154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022154).length < 2 ^ (prefixWord ++ tailWord_2022154).sum := by decide
  have hdescent : baseEnd_2022154 < baseStart_2022154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022184 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2022184 : Nat := 118140960795 + 2022184 * 2 ^ 59
def prefixEnd_2022184 : Nat := 4983230072969 + 3 ^ 40 * 2022184 * 2
def baseEnd_2022184 : Nat := 1038352363831621429500151

theorem tailTrace_2022184 : CollatzResearch.WordTrace tailWord_2022184 prefixEnd_2022184 1038352363831621429500151 := by
  unfold tailWord_2022184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36877554852990102188336803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49170073137320136251115737 36877554852990102188336803)
  ·
    refine ⟨55316332279485153282505205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36877554852990102188336803 55316332279485153282505205)
    ·
      refine ⟨5185906151201733120234863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55316332279485153282505205 5185906151201733120234863)
      ·
        refine ⟨7778859226802599680352295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5185906151201733120234863 7778859226802599680352295)
        ·
          refine ⟨11668288840203899520528443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778859226802599680352295 11668288840203899520528443)
          ·
            refine ⟨17502433260305849280792665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11668288840203899520528443 17502433260305849280792665)
            ·
              refine ⟨13126824945229386960594499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17502433260305849280792665 13126824945229386960594499)
              ·
                refine ⟨19690237417844080440891749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13126824945229386960594499 19690237417844080440891749)
                ·
                  refine ⟨3691919515845765082667203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19690237417844080440891749 3691919515845765082667203)
                  ·
                    refine ⟨5537879273768647624000805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3691919515845765082667203 5537879273768647624000805)
                    ·
                      refine ⟨1038352363831621429500151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5537879273768647624000805 1038352363831621429500151)
                      ·
                        rfl

theorem cell23_2022184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2022184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022184 prefixEnd_2022184 := by exact prefixLift 2022184
  have htrace : WordTrace (prefixWord ++ tailWord_2022184) baseStart_2022184 baseEnd_2022184 := by
    simpa [prefixWord, tailWord_2022184, baseEnd_2022184] using wordTrace_append hprefix tailTrace_2022184
  have hstable : (prefixWord ++ tailWord_2022184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022184).length < 2 ^ (prefixWord ++ tailWord_2022184).sum := by decide
  have hdescent : baseEnd_2022184 < baseStart_2022184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022187 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 3]
def baseStart_2022187 : Nat := 118140960795 + 2022187 * 2 ^ 59
def prefixEnd_2022187 : Nat := 4983230072969 + 3 ^ 40 * 2022187 * 2
def baseEnd_2022187 : Nat := 1038353904273584917762637

theorem tailTrace_2022187 : CollatzResearch.WordTrace tailWord_2022187 prefixEnd_2022187 1038353904273584917762637 := by
  unfold tailWord_2022187
  simp only [CollatzResearch.WordTrace]
  refine ⟨73755219124969335889032815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49170146083312890592688543 73755219124969335889032815)
  ·
    refine ⟨110632828687454003833549223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73755219124969335889032815 110632828687454003833549223)
    ·
      refine ⟨165949243031181005750323835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110632828687454003833549223 165949243031181005750323835)
      ·
        refine ⟨248923864546771508625485753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165949243031181005750323835 248923864546771508625485753)
        ·
          refine ⟨186692898410078631469114315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248923864546771508625485753 186692898410078631469114315)
          ·
            refine ⟨280039347615117947203671473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186692898410078631469114315 280039347615117947203671473)
            ·
              refine ⟨210029510711338460402753605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280039347615117947203671473 210029510711338460402753605)
              ·
                refine ⟨39380533258375961325516301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210029510711338460402753605 39380533258375961325516301)
                ·
                  refine ⟨14767699971890985497068613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39380533258375961325516301 14767699971890985497068613)
                  ·
                    refine ⟨2768943744729559780700365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14767699971890985497068613 2768943744729559780700365)
                    ·
                      refine ⟨1038353904273584917762637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2768943744729559780700365 1038353904273584917762637)
                      ·
                        rfl

theorem cell23_2022187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 3].length) (baseStart_2022187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022187 prefixEnd_2022187 := by exact prefixLift 2022187
  have htrace : WordTrace (prefixWord ++ tailWord_2022187) baseStart_2022187 baseEnd_2022187 := by
    simpa [prefixWord, tailWord_2022187, baseEnd_2022187] using wordTrace_append hprefix tailTrace_2022187
  have hstable : (prefixWord ++ tailWord_2022187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022187).length < 2 ^ (prefixWord ++ tailWord_2022187).sum := by decide
  have hdescent : baseEnd_2022187 < baseStart_2022187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022251 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 3]
def baseStart_2022251 : Nat := 118140960795 + 2022251 * 2 ^ 59
def prefixEnd_2022251 : Nat := 4983230072969 + 3 ^ 40 * 2022251 * 2
def baseEnd_2022251 : Nat := 1038386767035472667362343

theorem tailTrace_2022251 : CollatzResearch.WordTrace tailWord_2022251 prefixEnd_2022251 1038386767035472667362343 := by
  unfold tailWord_2022251
  simp only [CollatzResearch.WordTrace]
  refine ⟨73757553396737474819362607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49171702264491649879575071 73757553396737474819362607)
  ·
    refine ⟨110636330095106212229043911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73757553396737474819362607 110636330095106212229043911)
    ·
      refine ⟨165954495142659318343565867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110636330095106212229043911 165954495142659318343565867)
      ·
        refine ⟨248931742713988977515348801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165954495142659318343565867 248931742713988977515348801)
        ·
          refine ⟨186698807035491733136511601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248931742713988977515348801 186698807035491733136511601)
          ·
            refine ⟨140024105276618799852383701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186698807035491733136511601 140024105276618799852383701)
            ·
              refine ⟨3281814967420753121540243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 140024105276618799852383701 3281814967420753121540243)
              ·
                refine ⟨4922722451131129682310365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281814967420753121540243 4922722451131129682310365)
                ·
                  refine ⟨1846020919174173630866387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4922722451131129682310365 1846020919174173630866387)
                  ·
                    refine ⟨2769031378761260446299581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1846020919174173630866387 2769031378761260446299581)
                    ·
                      refine ⟨1038386767035472667362343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2769031378761260446299581 1038386767035472667362343)
                      ·
                        rfl

theorem cell23_2022251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 1, 3].length) (baseStart_2022251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022251 prefixEnd_2022251 := by exact prefixLift 2022251
  have htrace : WordTrace (prefixWord ++ tailWord_2022251) baseStart_2022251 baseEnd_2022251 := by
    simpa [prefixWord, tailWord_2022251, baseEnd_2022251] using wordTrace_append hprefix tailTrace_2022251
  have hstable : (prefixWord ++ tailWord_2022251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022251).length < 2 ^ (prefixWord ++ tailWord_2022251).sum := by decide
  have hdescent : baseEnd_2022251 < baseStart_2022251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022284 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_2022284 : Nat := 118140960795 + 2022284 * 2 ^ 59
def prefixEnd_2022284 : Nat := 4983230072969 + 3 ^ 40 * 2022284 * 2
def baseEnd_2022284 : Nat := 346134570632357012749897

theorem tailTrace_2022284 : CollatzResearch.WordTrace tailWord_2022284 prefixEnd_2022284 346134570632357012749897 := by
  unfold tailWord_2022284
  simp only [CollatzResearch.WordTrace]
  refine ⟨36879378502808960727656953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49172504670411947636875937 36879378502808960727656953)
  ·
    refine ⟨27659533877106720545742715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36879378502808960727656953 27659533877106720545742715)
    ·
      refine ⟨41489300815660080818614073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27659533877106720545742715 41489300815660080818614073)
      ·
        refine ⟨31116975611745060613960555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41489300815660080818614073 31116975611745060613960555)
        ·
          refine ⟨46675463417617590920940833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31116975611745060613960555 46675463417617590920940833)
          ·
            refine ⟨35006597563213193190705625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46675463417617590920940833 35006597563213193190705625)
            ·
              refine ⟨26254948172409894893029219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35006597563213193190705625 26254948172409894893029219)
              ·
                refine ⟨39382422258614842339543829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26254948172409894893029219 39382422258614842339543829)
                ·
                  refine ⟨1846051043372570734666117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39382422258614842339543829 1846051043372570734666117)
                  ·
                    refine ⟨346134570632357012749897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1846051043372570734666117 346134570632357012749897)
                    ·
                      rfl

theorem cell23_2022284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_2022284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022284 prefixEnd_2022284 := by exact prefixLift 2022284
  have htrace : WordTrace (prefixWord ++ tailWord_2022284) baseStart_2022284 baseEnd_2022284 := by
    simpa [prefixWord, tailWord_2022284, baseEnd_2022284] using wordTrace_append hprefix tailTrace_2022284
  have hstable : (prefixWord ++ tailWord_2022284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022284).length < 2 ^ (prefixWord ++ tailWord_2022284).sum := by decide
  have hdescent : baseEnd_2022284 < baseStart_2022284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022291 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 7, 2, 2]
def baseStart_2022291 : Nat := 118140960795 + 2022291 * 2 ^ 59
def prefixEnd_2022291 : Nat := 4983230072969 + 3 ^ 40 * 2022291 * 2
def baseEnd_2022291 : Nat := 1038407306261652510862159

theorem tailTrace_2022291 : CollatzResearch.WordTrace tailWord_2022291 prefixEnd_2022291 1038407306261652510862159 := by
  unfold tailWord_2022291
  simp only [CollatzResearch.WordTrace]
  refine ⟨73759012316592561650818727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49172674877728374433879151 73759012316592561650818727)
  ·
    refine ⟨110638518474888842476228091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73759012316592561650818727 110638518474888842476228091)
    ·
      refine ⟨165957777712333263714342137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110638518474888842476228091 165957777712333263714342137)
      ·
        refine ⟨124468333284249947785756603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165957777712333263714342137 124468333284249947785756603)
        ·
          refine ⟨186702499926374921678634905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124468333284249947785756603 186702499926374921678634905)
          ·
            refine ⟨140026874944781191258976179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186702499926374921678634905 140026874944781191258976179)
            ·
              refine ⟨210040312417171786888464269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140026874944781191258976179 210040312417171786888464269)
              ·
                refine ⟨78765117156439420083174101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210040312417171786888464269 78765117156439420083174101)
                ·
                  refine ⟨1846057433354048908199393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 78765117156439420083174101 1846057433354048908199393)
                  ·
                    refine ⟨1384543075015536681149545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1846057433354048908199393 1384543075015536681149545)
                    ·
                      refine ⟨1038407306261652510862159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384543075015536681149545 1038407306261652510862159)
                      ·
                        rfl

theorem cell23_2022291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 2, 2].length) (baseStart_2022291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022291 prefixEnd_2022291 := by exact prefixLift 2022291
  have htrace : WordTrace (prefixWord ++ tailWord_2022291) baseStart_2022291 baseEnd_2022291 := by
    simpa [prefixWord, tailWord_2022291, baseEnd_2022291] using wordTrace_append hprefix tailTrace_2022291
  have hstable : (prefixWord ++ tailWord_2022291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022291).length < 2 ^ (prefixWord ++ tailWord_2022291).sum := by decide
  have hdescent : baseEnd_2022291 < baseStart_2022291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022308 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_2022308 : Nat := 118140960795 + 2022308 * 2 ^ 59
def prefixEnd_2022308 : Nat := 4983230072969 + 3 ^ 40 * 2022308 * 2
def baseEnd_2022308 : Nat := 1038416035432778944349581

theorem tailTrace_2022308 : CollatzResearch.WordTrace tailWord_2022308 prefixEnd_2022308 1038416035432778944349581 := by
  unfold tailWord_2022308
  simp only [CollatzResearch.WordTrace]
  refine ⟨36879816178765486777093789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49173088238353982369458385 36879816178765486777093789)
  ·
    refine ⟨13829931067037057541410171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36879816178765486777093789 13829931067037057541410171)
    ·
      refine ⟨20744896600555586312115257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13829931067037057541410171 20744896600555586312115257)
      ·
        refine ⟨15558672450416689734086443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20744896600555586312115257 15558672450416689734086443)
        ·
          refine ⟨23338008675625034601129665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15558672450416689734086443 23338008675625034601129665)
          ·
            refine ⟨17503506506718775950847249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23338008675625034601129665 17503506506718775950847249)
            ·
              refine ⟨13127629880039081963135437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17503506506718775950847249 13127629880039081963135437)
              ·
                refine ⟨4922861205014655736175789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13127629880039081963135437 4922861205014655736175789)
                ·
                  refine ⟨1846072951880495901065921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4922861205014655736175789 1846072951880495901065921)
                  ·
                    refine ⟨1384554713910371925799441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1846072951880495901065921 1384554713910371925799441)
                    ·
                      refine ⟨1038416035432778944349581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384554713910371925799441 1038416035432778944349581)
                      ·
                        rfl

theorem cell23_2022308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_2022308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022308 prefixEnd_2022308 := by exact prefixLift 2022308
  have htrace : WordTrace (prefixWord ++ tailWord_2022308) baseStart_2022308 baseEnd_2022308 := by
    simpa [prefixWord, tailWord_2022308, baseEnd_2022308] using wordTrace_append hprefix tailTrace_2022308
  have hstable : (prefixWord ++ tailWord_2022308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022308).length < 2 ^ (prefixWord ++ tailWord_2022308).sum := by decide
  have hdescent : baseEnd_2022308 < baseStart_2022308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022384 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_2022384 : Nat := 118140960795 + 2022384 * 2 ^ 59
def prefixEnd_2022384 : Nat := 4983230072969 + 3 ^ 40 * 2022384 * 2
def baseEnd_2022384 : Nat := 1038455059962520646999231

theorem tailTrace_2022384 : CollatzResearch.WordTrace tailWord_2022384 prefixEnd_2022384 1038455059962520646999231 := by
  unfold tailWord_2022384
  simp only [CollatzResearch.WordTrace]
  refine ⟨36881202152627819266977103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49174936203503759022636137 36881202152627819266977103)
  ·
    refine ⟨55321803228941728900465655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36881202152627819266977103 55321803228941728900465655)
    ·
      refine ⟨82982704843412593350698483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55321803228941728900465655 82982704843412593350698483)
      ·
        refine ⟨124474057265118890026047725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82982704843412593350698483 124474057265118890026047725)
        ·
          refine ⟨46677771474419583759767897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124474057265118890026047725 46677771474419583759767897)
          ·
            refine ⟨35008328605814687819825923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46677771474419583759767897 35008328605814687819825923)
            ·
              refine ⟨52512492908722031729738885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35008328605814687819825923 52512492908722031729738885)
              ·
                refine ⟨9846092420385380949326041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52512492908722031729738885 9846092420385380949326041)
                ·
                  refine ⟨7384569315289035711994531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9846092420385380949326041 7384569315289035711994531)
                  ·
                    refine ⟨11076853972933553567991797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7384569315289035711994531 11076853972933553567991797)
                    ·
                      refine ⟨1038455059962520646999231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11076853972933553567991797 1038455059962520646999231)
                      ·
                        rfl

theorem cell23_2022384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_2022384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022384 prefixEnd_2022384 := by exact prefixLift 2022384
  have htrace : WordTrace (prefixWord ++ tailWord_2022384) baseStart_2022384 baseEnd_2022384 := by
    simpa [prefixWord, tailWord_2022384, baseEnd_2022384] using wordTrace_append hprefix tailTrace_2022384
  have hstable : (prefixWord ++ tailWord_2022384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022384).length < 2 ^ (prefixWord ++ tailWord_2022384).sum := by decide
  have hdescent : baseEnd_2022384 < baseStart_2022384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022385 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 1, 3, 2]
def baseStart_2022385 : Nat := 118140960795 + 2022385 * 2 ^ 59
def prefixEnd_2022385 : Nat := 4983230072969 + 3 ^ 40 * 2022385 * 2
def baseEnd_2022385 : Nat := 1038455573443175143086727

theorem tailTrace_2022385 : CollatzResearch.WordTrace tailWord_2022385 prefixEnd_2022385 1038455573443175143086727 := by
  unfold tailWord_2022385
  simp only [CollatzResearch.WordTrace]
  refine ⟨73762440778252015704740609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49174960518834677136493739 73762440778252015704740609)
  ·
    refine ⟨55321830583689011778555457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73762440778252015704740609 55321830583689011778555457)
    ·
      refine ⟨41491372937766758833916593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55321830583689011778555457 41491372937766758833916593)
      ·
        refine ⟨31118529703325069125437445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41491372937766758833916593 31118529703325069125437445)
        ·
          refine ⟨5834724319373450461019521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31118529703325069125437445 5834724319373450461019521)
          ·
            refine ⟨4376043239530087845764641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5834724319373450461019521 4376043239530087845764641)
            ·
              refine ⟨3282032429647565884323481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4376043239530087845764641 3282032429647565884323481)
              ·
                refine ⟨2461524322235674413242611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282032429647565884323481 2461524322235674413242611)
                ·
                  refine ⟨3692286483353511619863917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461524322235674413242611 3692286483353511619863917)
                  ·
                    refine ⟨1384607431257566857448969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3692286483353511619863917 1384607431257566857448969)
                    ·
                      refine ⟨1038455573443175143086727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384607431257566857448969 1038455573443175143086727)
                      ·
                        rfl

theorem cell23_2022385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_2022385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022385 prefixEnd_2022385 := by exact prefixLift 2022385
  have htrace : WordTrace (prefixWord ++ tailWord_2022385) baseStart_2022385 baseEnd_2022385 := by
    simpa [prefixWord, tailWord_2022385, baseEnd_2022385] using wordTrace_append hprefix tailTrace_2022385
  have hstable : (prefixWord ++ tailWord_2022385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022385).length < 2 ^ (prefixWord ++ tailWord_2022385).sum := by decide
  have hdescent : baseEnd_2022385 < baseStart_2022385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022394 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_2022394 : Nat := 118140960795 + 2022394 * 2 ^ 59
def prefixEnd_2022394 : Nat := 4983230072969 + 3 ^ 40 * 2022394 * 2
def baseEnd_2022394 : Nat := 1038460194769065607874185

theorem tailTrace_2022394 : CollatzResearch.WordTrace tailWord_2022394 prefixEnd_2022394 1038460194769065607874185 := by
  unfold tailWord_2022394
  simp only [CollatzResearch.WordTrace]
  refine ⟨18440692258804852560454559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49175179356812940161212157 18440692258804852560454559)
  ·
    refine ⟨27661038388207278840681839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18440692258804852560454559 27661038388207278840681839)
    ·
      refine ⟨41491557582310918261022759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27661038388207278840681839 41491557582310918261022759)
      ·
        refine ⟨62237336373466377391534139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41491557582310918261022759 62237336373466377391534139)
        ·
          refine ⟨93356004560199566087301209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62237336373466377391534139 93356004560199566087301209)
          ·
            refine ⟨70017003420149674565475907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93356004560199566087301209 70017003420149674565475907)
            ·
              refine ⟨105025505130224511848213861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70017003420149674565475907 105025505130224511848213861)
              ·
                refine ⟨19692282211917095971540099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105025505130224511848213861 19692282211917095971540099)
                ·
                  refine ⟨29538423317875643957310149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19692282211917095971540099 29538423317875643957310149)
                  ·
                    refine ⟨5538454372101683241995653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29538423317875643957310149 5538454372101683241995653)
                    ·
                      refine ⟨1038460194769065607874185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5538454372101683241995653 1038460194769065607874185)
                      ·
                        rfl

theorem cell23_2022394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_2022394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022394 prefixEnd_2022394 := by exact prefixLift 2022394
  have htrace : WordTrace (prefixWord ++ tailWord_2022394) baseStart_2022394 baseEnd_2022394 := by
    simpa [prefixWord, tailWord_2022394, baseEnd_2022394] using wordTrace_append hprefix tailTrace_2022394
  have hstable : (prefixWord ++ tailWord_2022394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022394).length < 2 ^ (prefixWord ++ tailWord_2022394).sum := by decide
  have hdescent : baseEnd_2022394 < baseStart_2022394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022401 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2022401 : Nat := 118140960795 + 2022401 * 2 ^ 59
def prefixEnd_2022401 : Nat := 4983230072969 + 3 ^ 40 * 2022401 * 2
def baseEnd_2022401 : Nat := 1038463789133647080486653

theorem tailTrace_2022401 : CollatzResearch.WordTrace tailWord_2022401 prefixEnd_2022401 1038463789133647080486653 := by
  unfold tailWord_2022401
  simp only [CollatzResearch.WordTrace]
  refine ⟨73763024346194050437323057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49175349564129366958215371 73763024346194050437323057)
  ·
    refine ⟨55322268259645537827992293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73763024346194050437323057 55322268259645537827992293)
    ·
      refine ⟨10372925298683538342748555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55322268259645537827992293 10372925298683538342748555)
      ·
        refine ⟨15559387948025307514122833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10372925298683538342748555 15559387948025307514122833)
        ·
          refine ⟨11669540961018980635592125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15559387948025307514122833 11669540961018980635592125)
          ·
            refine ⟨4376077860382117738347047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11669540961018980635592125 4376077860382117738347047)
            ·
              refine ⟨6564116790573176607520571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376077860382117738347047 6564116790573176607520571)
              ·
                refine ⟨9846175185859764911280857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564116790573176607520571 9846175185859764911280857)
                ·
                  refine ⟨7384631389394823683460643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9846175185859764911280857 7384631389394823683460643)
                  ·
                    refine ⟨11076947084092235525190965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7384631389394823683460643 11076947084092235525190965)
                    ·
                      refine ⟨1038463789133647080486653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11076947084092235525190965 1038463789133647080486653)
                      ·
                        rfl

theorem cell23_2022401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2022401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022401 prefixEnd_2022401 := by exact prefixLift 2022401
  have htrace : WordTrace (prefixWord ++ tailWord_2022401) baseStart_2022401 baseEnd_2022401 := by
    simpa [prefixWord, tailWord_2022401, baseEnd_2022401] using wordTrace_append hprefix tailTrace_2022401
  have hstable : (prefixWord ++ tailWord_2022401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022401).length < 2 ^ (prefixWord ++ tailWord_2022401).sum := by decide
  have hdescent : baseEnd_2022401 < baseStart_2022401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022421 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 7]
def baseStart_2022421 : Nat := 118140960795 + 2022421 * 2 ^ 59
def prefixEnd_2022421 : Nat := 4983230072969 + 3 ^ 40 * 2022421 * 2
def baseEnd_2022421 : Nat := 115386006527415222470729

theorem tailTrace_2022421 : CollatzResearch.WordTrace tailWord_2022421 prefixEnd_2022421 115386006527415222470729 := by
  unfold tailWord_2022421
  simp only [CollatzResearch.WordTrace]
  refine ⟨73763753806121593853051117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49175835870747729235367411 73763753806121593853051117)
  ·
    refine ⟨27661407677295597694894169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73763753806121593853051117 27661407677295597694894169)
    ·
      refine ⟨20746055757971698271170627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27661407677295597694894169 20746055757971698271170627)
      ·
        refine ⟨31119083636957547406755941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20746055757971698271170627 31119083636957547406755941)
        ·
          refine ⟨5834828181929540138766739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31119083636957547406755941 5834828181929540138766739)
          ·
            refine ⟨8752242272894310208150109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834828181929540138766739 8752242272894310208150109)
            ·
              refine ⟨3282090852335366328056291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8752242272894310208150109 3282090852335366328056291)
              ·
                refine ⟨4923136278503049492084437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282090852335366328056291 4923136278503049492084437)
                ·
                  refine ⟨115386006527415222470729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4923136278503049492084437 115386006527415222470729)
                  ·
                    rfl

theorem cell23_2022421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_2022421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022421 prefixEnd_2022421 := by exact prefixLift 2022421
  have htrace : WordTrace (prefixWord ++ tailWord_2022421) baseStart_2022421 baseEnd_2022421 := by
    simpa [prefixWord, tailWord_2022421, baseEnd_2022421] using wordTrace_append hprefix tailTrace_2022421
  have hstable : (prefixWord ++ tailWord_2022421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022421).length < 2 ^ (prefixWord ++ tailWord_2022421).sum := by decide
  have hdescent : baseEnd_2022421 < baseStart_2022421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022444 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_2022444 : Nat := 118140960795 + 2022444 * 2 ^ 59
def prefixEnd_2022444 : Nat := 4983230072969 + 3 ^ 40 * 2022444 * 2
def baseEnd_2022444 : Nat := 1038485868801790412248955

theorem tailTrace_2022444 : CollatzResearch.WordTrace tailWord_2022444 prefixEnd_2022444 1038485868801790412248955 := by
  unfold tailWord_2022444
  simp only [CollatzResearch.WordTrace]
  refine ⟨36882296342519134390569193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49176395123358845854092257 36882296342519134390569193)
  ·
    refine ⟨27661722256889350792926895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36882296342519134390569193 27661722256889350792926895)
    ·
      refine ⟨41492583385334026189390343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27661722256889350792926895 41492583385334026189390343)
      ·
        refine ⟨62238875078001039284085515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41492583385334026189390343 62238875078001039284085515)
        ·
          refine ⟨93358312617001558926128273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62238875078001039284085515 93358312617001558926128273)
          ·
            refine ⟨70018734462751169194596205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93358312617001558926128273 70018734462751169194596205)
            ·
              refine ⟨26257025423531688447973577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70018734462751169194596205 26257025423531688447973577)
              ·
                refine ⟨19692769067648766335980183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26257025423531688447973577 19692769067648766335980183)
                ·
                  refine ⟨29539153601473149503970275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19692769067648766335980183 29539153601473149503970275)
                  ·
                    refine ⟨44308730402209724255955413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29539153601473149503970275 44308730402209724255955413)
                    ·
                      refine ⟨1038485868801790412248955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44308730402209724255955413 1038485868801790412248955)
                      ·
                        rfl

theorem cell23_2022444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_2022444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022444 prefixEnd_2022444 := by exact prefixLift 2022444
  have htrace : WordTrace (prefixWord ++ tailWord_2022444) baseStart_2022444 baseEnd_2022444 := by
    simpa [prefixWord, tailWord_2022444, baseEnd_2022444] using wordTrace_append hprefix tailTrace_2022444
  have hstable : (prefixWord ++ tailWord_2022444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022444).length < 2 ^ (prefixWord ++ tailWord_2022444).sum := by decide
  have hdescent : baseEnd_2022444 < baseStart_2022444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022461 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2022461 : Nat := 118140960795 + 2022461 * 2 ^ 59
def prefixEnd_2022461 : Nat := 4983230072969 + 3 ^ 40 * 2022461 * 2
def baseEnd_2022461 : Nat := 1038494597972916845736377

theorem tailTrace_2022461 : CollatzResearch.WordTrace tailWord_2022461 prefixEnd_2022461 1038494597972916845736377 := by
  unfold tailWord_2022461
  simp only [CollatzResearch.WordTrace]
  refine ⟨73765212725976680684507237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49176808483984453789671491 73765212725976680684507237)
  ·
    refine ⟨13830977386120627628345107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73765212725976680684507237 13830977386120627628345107)
    ·
      refine ⟨20746466079180941442517661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13830977386120627628345107 20746466079180941442517661)
      ·
        refine ⟨7779924779692853040944123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20746466079180941442517661 7779924779692853040944123)
        ·
          refine ⟨11669887169539279561416185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7779924779692853040944123 11669887169539279561416185)
          ·
            refine ⟨8752415377154459671062139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11669887169539279561416185 8752415377154459671062139)
            ·
              refine ⟨13128623065731689506593209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752415377154459671062139 13128623065731689506593209)
              ·
                refine ⟨9846467299298767129944907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13128623065731689506593209 9846467299298767129944907)
                ·
                  refine ⟨14769700948948150694917361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9846467299298767129944907 14769700948948150694917361)
                  ·
                    refine ⟨11077275711711113021188021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14769700948948150694917361 11077275711711113021188021)
                    ·
                      refine ⟨1038494597972916845736377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11077275711711113021188021 1038494597972916845736377)
                      ·
                        rfl

theorem cell23_2022461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2022461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022461 prefixEnd_2022461 := by exact prefixLift 2022461
  have htrace : WordTrace (prefixWord ++ tailWord_2022461) baseStart_2022461 baseEnd_2022461 := by
    simpa [prefixWord, tailWord_2022461, baseEnd_2022461] using wordTrace_append hprefix tailTrace_2022461
  have hstable : (prefixWord ++ tailWord_2022461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022461).length < 2 ^ (prefixWord ++ tailWord_2022461).sum := by decide
  have hdescent : baseEnd_2022461 < baseStart_2022461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022488 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 2, 4, 2]
def baseStart_2022488 : Nat := 118140960795 + 2022488 * 2 ^ 59
def prefixEnd_2022488 : Nat := 4983230072969 + 3 ^ 40 * 2022488 * 2
def baseEnd_2022488 : Nat := 1038508461950588240098753

theorem tailTrace_2022488 : CollatzResearch.WordTrace tailWord_2022488 prefixEnd_2022488 1038508461950588240098753 := by
  unfold tailWord_2022488
  simp only [CollatzResearch.WordTrace]
  refine ⟨36883098748439432147870059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49177464997919242863826745 36883098748439432147870059)
  ·
    refine ⟨55324648122659148221805089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36883098748439432147870059 55324648122659148221805089)
    ·
      refine ⟨41493486091994361166353817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55324648122659148221805089 41493486091994361166353817)
      ·
        refine ⟨31120114568995770874765363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41493486091994361166353817 31120114568995770874765363)
        ·
          refine ⟨46680171853493656312148045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31120114568995770874765363 46680171853493656312148045)
          ·
            refine ⟨17505064445060121117055517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46680171853493656312148045 17505064445060121117055517)
            ·
              refine ⟨6564399166897545418895819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17505064445060121117055517 6564399166897545418895819)
              ·
                refine ⟨9846598750346318128343729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564399166897545418895819 9846598750346318128343729)
                ·
                  refine ⟨7384949062759738596257797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9846598750346318128343729 7384949062759738596257797)
                  ·
                    refine ⟨1384677949267450986798337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7384949062759738596257797 1384677949267450986798337)
                    ·
                      refine ⟨1038508461950588240098753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384677949267450986798337 1038508461950588240098753)
                      ·
                        rfl

theorem cell23_2022488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_2022488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022488 prefixEnd_2022488 := by exact prefixLift 2022488
  have htrace : WordTrace (prefixWord ++ tailWord_2022488) baseStart_2022488 baseEnd_2022488 := by
    simpa [prefixWord, tailWord_2022488, baseEnd_2022488] using wordTrace_append hprefix tailTrace_2022488
  have hstable : (prefixWord ++ tailWord_2022488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022488).length < 2 ^ (prefixWord ++ tailWord_2022488).sum := by decide
  have hdescent : baseEnd_2022488 < baseStart_2022488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022591 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_2022591 : Nat := 118140960795 + 2022591 * 2 ^ 59
def prefixEnd_2022591 : Nat := 4983230072969 + 3 ^ 40 * 2022591 * 2
def baseEnd_2022591 : Nat := 1038561350458001337110779

theorem tailTrace_2022591 : CollatzResearch.WordTrace tailWord_2022591 prefixEnd_2022591 1038561350458001337110779 := by
  unfold tailWord_2022591
  simp only [CollatzResearch.WordTrace]
  refine ⟨73769954215505712886739627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49179969477003808591159751 73769954215505712886739627)
  ·
    refine ⟨110654931323258569330109441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73769954215505712886739627 110654931323258569330109441)
    ·
      refine ⟨82991198492443926997582081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110654931323258569330109441 82991198492443926997582081)
      ·
        refine ⟨62243398869332945248186561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82991198492443926997582081 62243398869332945248186561)
        ·
          refine ⟨46682549151999708936139921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62243398869332945248186561 46682549151999708936139921)
          ·
            refine ⟨35011911863999781702104941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46682549151999708936139921 35011911863999781702104941)
            ·
              refine ⟨13129466948999918138289353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35011911863999781702104941 13129466948999918138289353)
              ·
                refine ⟨9847100211749938603717015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13129466948999918138289353 9847100211749938603717015)
                ·
                  refine ⟨14770650317624907905575523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9847100211749938603717015 14770650317624907905575523)
                  ·
                    refine ⟨22155975476437361858363285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14770650317624907905575523 22155975476437361858363285)
                    ·
                      refine ⟨1038561350458001337110779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22155975476437361858363285 1038561350458001337110779)
                      ·
                        rfl

theorem cell23_2022591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_2022591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022591 prefixEnd_2022591 := by exact prefixLift 2022591
  have htrace : WordTrace (prefixWord ++ tailWord_2022591) baseStart_2022591 baseEnd_2022591 := by
    simpa [prefixWord, tailWord_2022591, baseEnd_2022591] using wordTrace_append hprefix tailTrace_2022591
  have hstable : (prefixWord ++ tailWord_2022591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022591).length < 2 ^ (prefixWord ++ tailWord_2022591).sum := by decide
  have hdescent : baseEnd_2022591 < baseStart_2022591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022595 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 3, 2, 2]
def baseStart_2022595 : Nat := 118140960795 + 2022595 * 2 ^ 59
def prefixEnd_2022595 : Nat := 4983230072969 + 3 ^ 40 * 2022595 * 2
def baseEnd_2022595 : Nat := 1038563404380619321460761

theorem tailTrace_2022595 : CollatzResearch.WordTrace tailWord_2022595 prefixEnd_2022595 1038563404380619321460761 := by
  unfold tailWord_2022595
  simp only [CollatzResearch.WordTrace]
  refine ⟨73770100107491221569885239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49180066738327481046590159 73770100107491221569885239)
  ·
    refine ⟨110655150161236832354827859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73770100107491221569885239 110655150161236832354827859)
    ·
      refine ⟨165982725241855248532241789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110655150161236832354827859 165982725241855248532241789)
      ·
        refine ⟨62243521965695718199590671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165982725241855248532241789 62243521965695718199590671)
        ·
          refine ⟨93365282948543577299386007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62243521965695718199590671 93365282948543577299386007)
          ·
            refine ⟨140047924422815365949079011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93365282948543577299386007 140047924422815365949079011)
            ·
              refine ⟨210071886634223048923618517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140047924422815365949079011 210071886634223048923618517)
              ·
                refine ⟨4923559842989602709147309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 210071886634223048923618517 4923559842989602709147309)
                ·
                  refine ⟨1846334941121101015930241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4923559842989602709147309 1846334941121101015930241)
                  ·
                    refine ⟨1384751205840825761947681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1846334941121101015930241 1384751205840825761947681)
                    ·
                      refine ⟨1038563404380619321460761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384751205840825761947681 1038563404380619321460761)
                      ·
                        rfl

theorem cell23_2022595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_2022595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022595 prefixEnd_2022595 := by exact prefixLift 2022595
  have htrace : WordTrace (prefixWord ++ tailWord_2022595) baseStart_2022595 baseEnd_2022595 := by
    simpa [prefixWord, tailWord_2022595, baseEnd_2022595] using wordTrace_append hprefix tailTrace_2022595
  have hstable : (prefixWord ++ tailWord_2022595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022595).length < 2 ^ (prefixWord ++ tailWord_2022595).sum := by decide
  have hdescent : baseEnd_2022595 < baseStart_2022595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022612 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2022612 : Nat := 118140960795 + 2022612 * 2 ^ 59
def prefixEnd_2022612 : Nat := 4983230072969 + 3 ^ 40 * 2022612 * 2
def baseEnd_2022612 : Nat := 1038572133551745754948183

theorem tailTrace_2022612 : CollatzResearch.WordTrace tailWord_2022612 prefixEnd_2022612 1038572133551745754948183 := by
  unfold tailWord_2022612
  simp only [CollatzResearch.WordTrace]
  refine ⟨36885360074214816736627045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49180480098953088982169393 36885360074214816736627045)
  ·
    refine ⟨6916005013915278138117571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36885360074214816736627045 6916005013915278138117571)
    ·
      refine ⟨10374007520872917207176357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6916005013915278138117571 10374007520872917207176357)
      ·
        refine ⟨1945126410163671976345567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10374007520872917207176357 1945126410163671976345567)
        ·
          refine ⟨2917689615245507964518351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945126410163671976345567 2917689615245507964518351)
          ·
            refine ⟨4376534422868261946777527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917689615245507964518351 4376534422868261946777527)
            ·
              refine ⟨6564801634302392920166291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376534422868261946777527 6564801634302392920166291)
              ·
                refine ⟨9847202451453589380249437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564801634302392920166291 9847202451453589380249437)
                ·
                  refine ⟨3692700919295096017593539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9847202451453589380249437 3692700919295096017593539)
                  ·
                    refine ⟨5539051378942644026390309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3692700919295096017593539 5539051378942644026390309)
                    ·
                      refine ⟨1038572133551745754948183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5539051378942644026390309 1038572133551745754948183)
                      ·
                        rfl

theorem cell23_2022612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2022612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022612 prefixEnd_2022612 := by exact prefixLift 2022612
  have htrace : WordTrace (prefixWord ++ tailWord_2022612) baseStart_2022612 baseEnd_2022612 := by
    simpa [prefixWord, tailWord_2022612, baseEnd_2022612] using wordTrace_append hprefix tailTrace_2022612
  have hstable : (prefixWord ++ tailWord_2022612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022612).length < 2 ^ (prefixWord ++ tailWord_2022612).sum := by decide
  have hdescent : baseEnd_2022612 < baseStart_2022612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022615 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_2022615 : Nat := 118140960795 + 2022615 * 2 ^ 59
def prefixEnd_2022615 : Nat := 4983230072969 + 3 ^ 40 * 2022615 * 2
def baseEnd_2022615 : Nat := 1038573673993709243210669

theorem tailTrace_2022615 : CollatzResearch.WordTrace tailWord_2022615 prefixEnd_2022615 1038573673993709243210669 := by
  unfold tailWord_2022615
  simp only [CollatzResearch.WordTrace]
  refine ⟨73770829567418764985613299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49180553044945843323742199 73770829567418764985613299)
  ·
    refine ⟨110656244351128147478419949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73770829567418764985613299 110656244351128147478419949)
    ·
      refine ⟨41496091631673055304407481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110656244351128147478419949 41496091631673055304407481)
      ·
        refine ⟨31122068723754791478305611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41496091631673055304407481 31122068723754791478305611)
        ·
          refine ⟨46683103085632187217458417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31122068723754791478305611 46683103085632187217458417)
          ·
            refine ⟨35012327314224140413093813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46683103085632187217458417 35012327314224140413093813)
            ·
              refine ⟨3282405685708513163727545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35012327314224140413093813 3282405685708513163727545)
              ·
                refine ⟨2461804264281384872795659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282405685708513163727545 2461804264281384872795659)
                ·
                  refine ⟨3692706396422077309193489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461804264281384872795659 3692706396422077309193489)
                  ·
                    refine ⟨2769529797316557981895117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692706396422077309193489 2769529797316557981895117)
                    ·
                      refine ⟨1038573673993709243210669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2769529797316557981895117 1038573673993709243210669)
                      ·
                        rfl

theorem cell23_2022615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_2022615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022615 prefixEnd_2022615 := by exact prefixLift 2022615
  have htrace : WordTrace (prefixWord ++ tailWord_2022615) baseStart_2022615 baseEnd_2022615 := by
    simpa [prefixWord, tailWord_2022615, baseEnd_2022615] using wordTrace_append hprefix tailTrace_2022615
  have hstable : (prefixWord ++ tailWord_2022615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022615).length < 2 ^ (prefixWord ++ tailWord_2022615).sum := by decide
  have hdescent : baseEnd_2022615 < baseStart_2022615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022628 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_2022628 : Nat := 118140960795 + 2022628 * 2 ^ 59
def prefixEnd_2022628 : Nat := 4983230072969 + 3 ^ 40 * 2022628 * 2
def baseEnd_2022628 : Nat := 1038580349242217692348109

theorem tailTrace_2022628 : CollatzResearch.WordTrace tailWord_2022628 prefixEnd_2022628 1038580349242217692348109 := by
  unfold tailWord_2022628
  simp only [CollatzResearch.WordTrace]
  refine ⟨36885651858185834102918269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49180869144247778803891025 36885651858185834102918269)
  ·
    refine ⟨13832119446819687788594351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36885651858185834102918269 13832119446819687788594351)
    ·
      refine ⟨20748179170229531682891527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13832119446819687788594351 20748179170229531682891527)
      ·
        refine ⟨31122268755344297524337291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20748179170229531682891527 31122268755344297524337291)
        ·
          refine ⟨46683403133016446286505937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31122268755344297524337291 46683403133016446286505937)
          ·
            refine ⟨35012552349762334714879453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46683403133016446286505937 35012552349762334714879453)
            ·
              refine ⟨13129707131160875518079795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35012552349762334714879453 13129707131160875518079795)
              ·
                refine ⟨19694560696741313277119693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13129707131160875518079795 19694560696741313277119693)
                ·
                  refine ⟨7385460261277992478919885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19694560696741313277119693 7385460261277992478919885)
                  ·
                    refine ⟨2769547597979247179594957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7385460261277992478919885 2769547597979247179594957)
                    ·
                      refine ⟨1038580349242217692348109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2769547597979247179594957 1038580349242217692348109)
                      ·
                        rfl

theorem cell23_2022628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_2022628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022628 prefixEnd_2022628 := by exact prefixLift 2022628
  have htrace : WordTrace (prefixWord ++ tailWord_2022628) baseStart_2022628 baseEnd_2022628 := by
    simpa [prefixWord, tailWord_2022628, baseEnd_2022628] using wordTrace_append hprefix tailTrace_2022628
  have hstable : (prefixWord ++ tailWord_2022628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022628).length < 2 ^ (prefixWord ++ tailWord_2022628).sum := by decide
  have hdescent : baseEnd_2022628 < baseStart_2022628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022632 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_2022632 : Nat := 118140960795 + 2022632 * 2 ^ 59
def prefixEnd_2022632 : Nat := 4983230072969 + 3 ^ 40 * 2022632 * 2
def baseEnd_2022632 : Nat := 1038582403164835676698091

theorem tailTrace_2022632 : CollatzResearch.WordTrace tailWord_2022632 prefixEnd_2022632 1038582403164835676698091 := by
  unfold tailWord_2022632
  simp only [CollatzResearch.WordTrace]
  refine ⟨36885724804178588444491075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49180966405571451259321433 36885724804178588444491075)
  ·
    refine ⟨55328587206267882666736613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36885724804178588444491075 55328587206267882666736613)
    ·
      refine ⟨10374110101175228000013115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55328587206267882666736613 10374110101175228000013115)
      ·
        refine ⟨15561165151762842000019673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10374110101175228000013115 15561165151762842000019673)
        ·
          refine ⟨11670873863822131500014755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15561165151762842000019673 11670873863822131500014755)
          ·
            refine ⟨17506310795733197250022133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670873863822131500014755 17506310795733197250022133)
            ·
              refine ⟨1641216637099987242189575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17506310795733197250022133 1641216637099987242189575)
              ·
                refine ⟨2461824955649980863284363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641216637099987242189575 2461824955649980863284363)
                ·
                  refine ⟨3692737433474971294926545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461824955649980863284363 3692737433474971294926545)
                  ·
                    refine ⟨2769553075106228471194909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3692737433474971294926545 2769553075106228471194909)
                    ·
                      refine ⟨1038582403164835676698091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2769553075106228471194909 1038582403164835676698091)
                      ·
                        rfl

theorem cell23_2022632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_2022632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022632 prefixEnd_2022632 := by exact prefixLift 2022632
  have htrace : WordTrace (prefixWord ++ tailWord_2022632) baseStart_2022632 baseEnd_2022632 := by
    simpa [prefixWord, tailWord_2022632, baseEnd_2022632] using wordTrace_append hprefix tailTrace_2022632
  have hstable : (prefixWord ++ tailWord_2022632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022632).length < 2 ^ (prefixWord ++ tailWord_2022632).sum := by decide
  have hdescent : baseEnd_2022632 < baseStart_2022632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022655 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 3, 3, 2]
def baseStart_2022655 : Nat := 118140960795 + 2022655 * 2 ^ 59
def prefixEnd_2022655 : Nat := 4983230072969 + 3 ^ 40 * 2022655 * 2
def baseEnd_2022655 : Nat := 1038594213219889086710485

theorem tailTrace_2022655 : CollatzResearch.WordTrace tailWord_2022655 prefixEnd_2022655 1038594213219889086710485 := by
  unfold tailWord_2022655
  simp only [CollatzResearch.WordTrace]
  refine ⟨73772288487273851817069419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49181525658182567878046279 73772288487273851817069419)
  ·
    refine ⟨110658432730910777725604129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73772288487273851817069419 110658432730910777725604129)
    ·
      refine ⟨82993824548183083294203097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110658432730910777725604129 82993824548183083294203097)
      ·
        refine ⟨62245368411137312470652323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82993824548183083294203097 62245368411137312470652323)
        ·
          refine ⟨93368052616705968705978485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62245368411137312470652323 93368052616705968705978485)
          ·
            refine ⟨8753254932816184566185483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93368052616705968705978485 8753254932816184566185483)
            ·
              refine ⟨13129882399224276849278225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8753254932816184566185483 13129882399224276849278225)
              ·
                refine ⟨9847411799418207636958669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13129882399224276849278225 9847411799418207636958669)
                ·
                  refine ⟨3692779424781827863859501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9847411799418207636958669 3692779424781827863859501)
                  ·
                    refine ⟨1384792284293185448947313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3692779424781827863859501 1384792284293185448947313)
                    ·
                      refine ⟨1038594213219889086710485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384792284293185448947313 1038594213219889086710485)
                      ·
                        rfl

theorem cell23_2022655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_2022655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022655 prefixEnd_2022655 := by exact prefixLift 2022655
  have htrace : WordTrace (prefixWord ++ tailWord_2022655) baseStart_2022655 baseEnd_2022655 := by
    simpa [prefixWord, tailWord_2022655, baseEnd_2022655] using wordTrace_append hprefix tailTrace_2022655
  have hstable : (prefixWord ++ tailWord_2022655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022655).length < 2 ^ (prefixWord ++ tailWord_2022655).sum := by decide
  have hdescent : baseEnd_2022655 < baseStart_2022655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022755 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 2, 5]
def baseStart_2022755 : Nat := 118140960795 + 2022755 * 2 ^ 59
def prefixEnd_2022755 : Nat := 4983230072969 + 3 ^ 40 * 2022755 * 2
def baseEnd_2022755 : Nat := 346215187095112898486675

theorem tailTrace_2022755 : CollatzResearch.WordTrace tailWord_2022755 prefixEnd_2022755 346215187095112898486675 := by
  unfold tailWord_2022755
  simp only [CollatzResearch.WordTrace]
  refine ⟨73775935786911568895709719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49183957191274379263806479 73775935786911568895709719)
  ·
    refine ⟨110663903680367353343564579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73775935786911568895709719 110663903680367353343564579)
    ·
      refine ⟨165995855520551030015346869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110663903680367353343564579 165995855520551030015346869)
      ·
        refine ⟨15562111455051659063938769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165995855520551030015346869 15562111455051659063938769)
        ·
          refine ⟨11671583591288744297954077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15562111455051659063938769 11671583591288744297954077)
          ·
            refine ⟨4376843846733279111732779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11671583591288744297954077 4376843846733279111732779)
            ·
              refine ⟨6565265770099918667599169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376843846733279111732779 6565265770099918667599169)
              ·
                refine ⟨4923949327574939000699377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565265770099918667599169 4923949327574939000699377)
                ·
                  refine ⟨3692961995681204250524533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4923949327574939000699377 3692961995681204250524533)
                  ·
                    refine ⟨346215187095112898486675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3692961995681204250524533 346215187095112898486675)
                    ·
                      rfl

theorem cell23_2022755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 5].length) (baseStart_2022755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022755 prefixEnd_2022755 := by exact prefixLift 2022755
  have htrace : WordTrace (prefixWord ++ tailWord_2022755) baseStart_2022755 baseEnd_2022755 := by
    simpa [prefixWord, tailWord_2022755, baseEnd_2022755] using wordTrace_append hprefix tailTrace_2022755
  have hstable : (prefixWord ++ tailWord_2022755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022755).length < 2 ^ (prefixWord ++ tailWord_2022755).sum := by decide
  have hdescent : baseEnd_2022755 < baseStart_2022755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022759 : List Nat := [1, 1, 5, 1, 4, 1, 3, 2, 5]
def baseStart_2022759 : Nat := 118140960795 + 2022759 * 2 ^ 59
def prefixEnd_2022759 : Nat := 4983230072969 + 3 ^ 40 * 2022759 * 2
def baseEnd_2022759 : Nat := 115405290578661853312223

theorem tailTrace_2022759 : CollatzResearch.WordTrace tailWord_2022759 prefixEnd_2022759 115405290578661853312223 := by
  unfold tailWord_2022759
  simp only [CollatzResearch.WordTrace]
  refine ⟨73776081678897077578855331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49184054452598051719236887 73776081678897077578855331)
  ·
    refine ⟨110664122518345616368282997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73776081678897077578855331 110664122518345616368282997)
    ·
      refine ⟨10374761486094901534526531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110664122518345616368282997 10374761486094901534526531)
      ·
        refine ⟨15562142229142352301789797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10374761486094901534526531 15562142229142352301789797)
        ·
          refine ⟨2917901667964191056585587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15562142229142352301789797 2917901667964191056585587)
          ·
            refine ⟨4376852501946286584878381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917901667964191056585587 4376852501946286584878381)
            ·
              refine ⟨1641319688229857469329393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4376852501946286584878381 1641319688229857469329393)
              ·
                refine ⟨1230989766172393101997045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641319688229857469329393 1230989766172393101997045)
                ·
                  refine ⟨115405290578661853312223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1230989766172393101997045 115405290578661853312223)
                  ·
                    rfl

theorem cell23_2022759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 5].length) (baseStart_2022759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022759 prefixEnd_2022759 := by exact prefixLift 2022759
  have htrace : WordTrace (prefixWord ++ tailWord_2022759) baseStart_2022759 baseEnd_2022759 := by
    simpa [prefixWord, tailWord_2022759, baseEnd_2022759] using wordTrace_append hprefix tailTrace_2022759
  have hstable : (prefixWord ++ tailWord_2022759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022759).length < 2 ^ (prefixWord ++ tailWord_2022759).sum := by decide
  have hdescent : baseEnd_2022759 < baseStart_2022759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022765 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2022765 : Nat := 118140960795 + 2022765 * 2 ^ 59
def prefixEnd_2022765 : Nat := 4983230072969 + 3 ^ 40 * 2022765 * 2
def baseEnd_2022765 : Nat := 1038650696091883656334979

theorem tailTrace_2022765 : CollatzResearch.WordTrace tailWord_2022765 prefixEnd_2022765 1038650696091883656334979 := by
  unfold tailWord_2022765
  simp only [CollatzResearch.WordTrace]
  refine ⟨73776300516875340603573749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49184200344583560402382499 73776300516875340603573749)
  ·
    refine ⟨6916528173457063181585039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73776300516875340603573749 6916528173457063181585039)
    ·
      refine ⟨10374792260185594772377559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6916528173457063181585039 10374792260185594772377559)
      ·
        refine ⟨15562188390278392158566339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10374792260185594772377559 15562188390278392158566339)
        ·
          refine ⟨23343282585417588237849509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15562188390278392158566339 23343282585417588237849509)
          ·
            refine ⟨4376865484765797794596783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23343282585417588237849509 4376865484765797794596783)
            ·
              refine ⟨6565298227148696691895175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376865484765797794596783 6565298227148696691895175)
              ·
                refine ⟨9847947340723045037842763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6565298227148696691895175 9847947340723045037842763)
                ·
                  refine ⟨14771921011084567556764145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9847947340723045037842763 14771921011084567556764145)
                  ·
                    refine ⟨11078940758313425667573109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14771921011084567556764145 11078940758313425667573109)
                    ·
                      refine ⟨1038650696091883656334979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11078940758313425667573109 1038650696091883656334979)
                      ·
                        rfl

theorem cell23_2022765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2022765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022765 prefixEnd_2022765 := by exact prefixLift 2022765
  have htrace : WordTrace (prefixWord ++ tailWord_2022765) baseStart_2022765 baseEnd_2022765 := by
    simpa [prefixWord, tailWord_2022765, baseEnd_2022765] using wordTrace_append hprefix tailTrace_2022765
  have hstable : (prefixWord ++ tailWord_2022765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022765).length < 2 ^ (prefixWord ++ tailWord_2022765).sum := by decide
  have hdescent : baseEnd_2022765 < baseStart_2022765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022775 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 1, 6, 2]
def baseStart_2022775 : Nat := 118140960795 + 2022775 * 2 ^ 59
def prefixEnd_2022775 : Nat := 4983230072969 + 3 ^ 40 * 2022775 * 2
def baseEnd_2022775 : Nat := 1038655830898428617209933

theorem tailTrace_2022775 : CollatzResearch.WordTrace tailWord_2022775 prefixEnd_2022775 1038655830898428617209933 := by
  unfold tailWord_2022775
  simp only [CollatzResearch.WordTrace]
  refine ⟨73776665246839112311437779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49184443497892741540958519 73776665246839112311437779)
  ·
    refine ⟨110664997870258668467156669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73776665246839112311437779 110664997870258668467156669)
    ·
      refine ⟨41499374201347000675183751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110664997870258668467156669 41499374201347000675183751)
      ·
        refine ⟨62249061302020501012775627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41499374201347000675183751 62249061302020501012775627)
        ·
          refine ⟨93373591953030751519163441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62249061302020501012775627 93373591953030751519163441)
          ·
            refine ⟨70030193964773063639372581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93373591953030751519163441 70030193964773063639372581)
            ·
              refine ⟨13130661368394949432382359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70030193964773063639372581 13130661368394949432382359)
              ·
                refine ⟨19695992052592424148573539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13130661368394949432382359 19695992052592424148573539)
                ·
                  refine ⟨29543988078888636222860309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19695992052592424148573539 29543988078888636222860309)
                  ·
                    refine ⟨1384874441197904822946577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29543988078888636222860309 1384874441197904822946577)
                    ·
                      refine ⟨1038655830898428617209933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1384874441197904822946577 1038655830898428617209933)
                      ·
                        rfl

theorem cell23_2022775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_2022775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022775 prefixEnd_2022775 := by exact prefixLift 2022775
  have htrace : WordTrace (prefixWord ++ tailWord_2022775) baseStart_2022775 baseEnd_2022775 := by
    simpa [prefixWord, tailWord_2022775, baseEnd_2022775] using wordTrace_append hprefix tailTrace_2022775
  have hstable : (prefixWord ++ tailWord_2022775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022775).length < 2 ^ (prefixWord ++ tailWord_2022775).sum := by decide
  have hdescent : baseEnd_2022775 < baseStart_2022775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022792 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_2022792 : Nat := 118140960795 + 2022792 * 2 ^ 59
def prefixEnd_2022792 : Nat := 4983230072969 + 3 ^ 40 * 2022792 * 2
def baseEnd_2022792 : Nat := 1038664560069555050697355

theorem tailTrace_2022792 : CollatzResearch.WordTrace tailWord_2022792 prefixEnd_2022792 1038664560069555050697355 := by
  unfold tailWord_2022792
  simp only [CollatzResearch.WordTrace]
  refine ⟨36888642643888762107403315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49184856858518349476537753 36888642643888762107403315)
  ·
    refine ⟨55332963965833143161104973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36888642643888762107403315 55332963965833143161104973)
    ·
      refine ⟨20749861487187428685414365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55332963965833143161104973 20749861487187428685414365)
      ·
        refine ⟨7781198057695285757030387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20749861487187428685414365 7781198057695285757030387)
        ·
          refine ⟨11671797086542928635545581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781198057695285757030387 11671797086542928635545581)
          ·
            refine ⟨4376923907453598238329593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11671797086542928635545581 4376923907453598238329593)
            ·
              refine ⟨3282692930590198678747195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4376923907453598238329593 3282692930590198678747195)
              ·
                refine ⟨4924039395885298018120793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282692930590198678747195 4924039395885298018120793)
                ·
                  refine ⟨3693029546913973513590595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4924039395885298018120793 3693029546913973513590595)
                  ·
                    refine ⟨5539544320370960270385893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3693029546913973513590595 5539544320370960270385893)
                    ·
                      refine ⟨1038664560069555050697355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5539544320370960270385893 1038664560069555050697355)
                      ·
                        rfl

theorem cell23_2022792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_2022792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022792 prefixEnd_2022792 := by exact prefixLift 2022792
  have htrace : WordTrace (prefixWord ++ tailWord_2022792) baseStart_2022792 baseEnd_2022792 := by
    simpa [prefixWord, tailWord_2022792, baseEnd_2022792] using wordTrace_append hprefix tailTrace_2022792
  have hstable : (prefixWord ++ tailWord_2022792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022792).length < 2 ^ (prefixWord ++ tailWord_2022792).sum := by decide
  have hdescent : baseEnd_2022792 < baseStart_2022792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022815 : List Nat := [1, 1, 2, 5, 1, 2, 1, 4, 6]
def baseStart_2022815 : Nat := 118140960795 + 2022815 * 2 ^ 59
def prefixEnd_2022815 : Nat := 4983230072969 + 3 ^ 40 * 2022815 * 2
def baseEnd_2022815 : Nat := 115408485569400940078861

theorem tailTrace_2022815 : CollatzResearch.WordTrace tailWord_2022815 prefixEnd_2022815 115408485569400940078861 := by
  unfold tailWord_2022815
  simp only [CollatzResearch.WordTrace]
  refine ⟨73778124166694199142893899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49185416111129466095262599 73778124166694199142893899)
  ·
    refine ⟨110667186250041298714340849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73778124166694199142893899 110667186250041298714340849)
    ·
      refine ⟨83000389687530974035755637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110667186250041298714340849 83000389687530974035755637)
      ·
        refine ⟨7781286533206028815852091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83000389687530974035755637 7781286533206028815852091)
        ·
          refine ⟨11671929799809043223778137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781286533206028815852091 11671929799809043223778137)
          ·
            refine ⟨8753947349856782417833603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11671929799809043223778137 8753947349856782417833603)
            ·
              refine ⟨13130921024785173626750405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8753947349856782417833603 13130921024785173626750405)
              ·
                refine ⟨2462047692147220055015701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13130921024785173626750405 2462047692147220055015701)
                ·
                  refine ⟨115408485569400940078861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2462047692147220055015701 115408485569400940078861)
                  ·
                    rfl

theorem cell23_2022815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 4, 6].length) (baseStart_2022815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022815 prefixEnd_2022815 := by exact prefixLift 2022815
  have htrace : WordTrace (prefixWord ++ tailWord_2022815) baseStart_2022815 baseEnd_2022815 := by
    simpa [prefixWord, tailWord_2022815, baseEnd_2022815] using wordTrace_append hprefix tailTrace_2022815
  have hstable : (prefixWord ++ tailWord_2022815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022815).length < 2 ^ (prefixWord ++ tailWord_2022815).sum := by decide
  have hdescent : baseEnd_2022815 < baseStart_2022815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022845 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2022845 : Nat := 118140960795 + 2022845 * 2 ^ 59
def prefixEnd_2022845 : Nat := 4983230072969 + 3 ^ 40 * 2022845 * 2
def baseEnd_2022845 : Nat := 346230591514747781111537

theorem tailTrace_2022845 : CollatzResearch.WordTrace tailWord_2022845 prefixEnd_2022845 346230591514747781111537 := by
  unfold tailWord_2022845
  simp only [CollatzResearch.WordTrace]
  refine ⟨73779218356585514266485989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49186145571057009510990659 73779218356585514266485989)
  ·
    refine ⟨13833603441859783924966123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73779218356585514266485989 13833603441859783924966123)
    ·
      refine ⟨20750405162789675887449185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13833603441859783924966123 20750405162789675887449185)
      ·
        refine ⟨15562803872092256915586889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20750405162789675887449185 15562803872092256915586889)
        ·
          refine ⟨11672102904069192686690167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15562803872092256915586889 11672102904069192686690167)
          ·
            refine ⟨17508154356103789030035251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11672102904069192686690167 17508154356103789030035251)
            ·
              refine ⟨26262231534155683545052877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17508154356103789030035251 26262231534155683545052877)
              ·
                refine ⟨9848336825308381329394829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26262231534155683545052877 9848336825308381329394829)
                ·
                  refine ⟨3693126309490642998523061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9848336825308381329394829 3693126309490642998523061)
                  ·
                    refine ⟨346230591514747781111537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3693126309490642998523061 346230591514747781111537)
                    ·
                      rfl

theorem cell23_2022845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2022845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022845 prefixEnd_2022845 := by exact prefixLift 2022845
  have htrace : WordTrace (prefixWord ++ tailWord_2022845) baseStart_2022845 baseEnd_2022845 := by
    simpa [prefixWord, tailWord_2022845, baseEnd_2022845] using wordTrace_append hprefix tailTrace_2022845
  have hstable : (prefixWord ++ tailWord_2022845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022845).length < 2 ^ (prefixWord ++ tailWord_2022845).sum := by decide
  have hdescent : baseEnd_2022845 < baseStart_2022845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022859 : List Nat := [1, 1, 1, 1, 3, 3, 3, 5, 1, 1, 3]
def baseStart_2022859 : Nat := 118140960795 + 2022859 * 2 ^ 59
def prefixEnd_2022859 : Nat := 4983230072969 + 3 ^ 40 * 2022859 * 2
def baseEnd_2022859 : Nat := 1038698963273406288559547

theorem tailTrace_2022859 : CollatzResearch.WordTrace tailWord_2022859 prefixEnd_2022859 1038698963273406288559547 := by
  unfold tailWord_2022859
  simp only [CollatzResearch.WordTrace]
  refine ⟨73779728978534794657495631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49186485985689863104997087 73779728978534794657495631)
  ·
    refine ⟨110669593467802191986243447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73779728978534794657495631 110669593467802191986243447)
    ·
      refine ⟨166004390201703287979365171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110669593467802191986243447 166004390201703287979365171)
      ·
        refine ⟨249006585302554931969047757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166004390201703287979365171 249006585302554931969047757)
        ·
          refine ⟨93377469488458099488392909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249006585302554931969047757 93377469488458099488392909)
          ·
            refine ⟨35016551058171787308147341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93377469488458099488392909 35016551058171787308147341)
            ·
              refine ⟨13131206646814420240555253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35016551058171787308147341 13131206646814420240555253)
              ·
                refine ⟨1231050623138851897552055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13131206646814420240555253 1231050623138851897552055)
                ·
                  refine ⟨1846575934708277846328083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231050623138851897552055 1846575934708277846328083)
                  ·
                    refine ⟨2769863902062416769492125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1846575934708277846328083 2769863902062416769492125)
                    ·
                      refine ⟨1038698963273406288559547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2769863902062416769492125 1038698963273406288559547)
                      ·
                        rfl

theorem cell23_2022859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 5, 1, 1, 3].length) (baseStart_2022859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022859 prefixEnd_2022859 := by exact prefixLift 2022859
  have htrace : WordTrace (prefixWord ++ tailWord_2022859) baseStart_2022859 baseEnd_2022859 := by
    simpa [prefixWord, tailWord_2022859, baseEnd_2022859] using wordTrace_append hprefix tailTrace_2022859
  have hstable : (prefixWord ++ tailWord_2022859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022859).length < 2 ^ (prefixWord ++ tailWord_2022859).sum := by decide
  have hdescent : baseEnd_2022859 < baseStart_2022859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022919 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2022919 : Nat := 118140960795 + 2022919 * 2 ^ 59
def prefixEnd_2022919 : Nat := 4983230072969 + 3 ^ 40 * 2022919 * 2
def baseEnd_2022919 : Nat := 1038729772112676053809271

theorem tailTrace_2022919 : CollatzResearch.WordTrace tailWord_2022919 prefixEnd_2022919 1038729772112676053809271 := by
  unfold tailWord_2022919
  simp only [CollatzResearch.WordTrace]
  refine ⟨73781917358317424904679811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49187944905544949936453207 73781917358317424904679811)
  ·
    refine ⟨110672876037476137357019717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73781917358317424904679811 110672876037476137357019717)
    ·
      refine ⟨20751164257026775754441197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110672876037476137357019717 20751164257026775754441197)
      ·
        refine ⟨7781686596385040907915449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20751164257026775754441197 7781686596385040907915449)
        ·
          refine ⟨5836264947288780680936587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7781686596385040907915449 5836264947288780680936587)
          ·
            refine ⟨8754397420933171021404881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836264947288780680936587 8754397420933171021404881)
            ·
              refine ⟨6565798065699878266053661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8754397420933171021404881 6565798065699878266053661)
              ·
                refine ⟨2462174274637454349770123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6565798065699878266053661 2462174274637454349770123)
                ·
                  refine ⟨3693261411956181524655185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462174274637454349770123 3693261411956181524655185)
                  ·
                    refine ⟨2769946058967136143491389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3693261411956181524655185 2769946058967136143491389)
                    ·
                      refine ⟨1038729772112676053809271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2769946058967136143491389 1038729772112676053809271)
                      ·
                        rfl

theorem cell23_2022919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2022919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022919 prefixEnd_2022919 := by exact prefixLift 2022919
  have htrace : WordTrace (prefixWord ++ tailWord_2022919) baseStart_2022919 baseEnd_2022919 := by
    simpa [prefixWord, tailWord_2022919, baseEnd_2022919] using wordTrace_append hprefix tailTrace_2022919
  have hstable : (prefixWord ++ tailWord_2022919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022919).length < 2 ^ (prefixWord ++ tailWord_2022919).sum := by decide
  have hdescent : baseEnd_2022919 < baseStart_2022919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022966 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_2022966 : Nat := 118140960795 + 2022966 * 2 ^ 59
def prefixEnd_2022966 : Nat := 4983230072969 + 3 ^ 40 * 2022966 * 2
def baseEnd_2022966 : Nat := 1038753905703437369921555

theorem tailTrace_2022966 : CollatzResearch.WordTrace tailWord_2022966 prefixEnd_2022966 1038753905703437369921555 := by
  unfold tailWord_2022966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611476974321696995727547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49189087726098101287760501 4611476974321696995727547)
  ·
    refine ⟨6917215461482545493591321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4611476974321696995727547 6917215461482545493591321)
    ·
      refine ⟨5187911596111909120193491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6917215461482545493591321 5187911596111909120193491)
      ·
        refine ⟨7781867394167863680290237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187911596111909120193491 7781867394167863680290237)
        ·
          refine ⟨2918200272812948880108839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7781867394167863680290237 2918200272812948880108839)
          ·
            refine ⟨4377300409219423320163259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918200272812948880108839 4377300409219423320163259)
            ·
              refine ⟨6565950613829134980244889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4377300409219423320163259 6565950613829134980244889)
              ·
                refine ⟨4924462960371851235183667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565950613829134980244889 4924462960371851235183667)
                ·
                  refine ⟨7386694440557776852775501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4924462960371851235183667 7386694440557776852775501)
                  ·
                    refine ⟨2770010415209166319790813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7386694440557776852775501 2770010415209166319790813)
                    ·
                      refine ⟨1038753905703437369921555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2770010415209166319790813 1038753905703437369921555)
                      ·
                        rfl

theorem cell23_2022966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_2022966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022966 prefixEnd_2022966 := by exact prefixLift 2022966
  have htrace : WordTrace (prefixWord ++ tailWord_2022966) baseStart_2022966 baseEnd_2022966 := by
    simpa [prefixWord, tailWord_2022966, baseEnd_2022966] using wordTrace_append hprefix tailTrace_2022966
  have hstable : (prefixWord ++ tailWord_2022966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022966).length < 2 ^ (prefixWord ++ tailWord_2022966).sum := by decide
  have hdescent : baseEnd_2022966 < baseStart_2022966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022985 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_2022985 : Nat := 118140960795 + 2022985 * 2 ^ 59
def prefixEnd_2022985 : Nat := 4983230072969 + 3 ^ 40 * 2022985 * 2
def baseEnd_2022985 : Nat := 1038763661835872795583967

theorem tailTrace_2022985 : CollatzResearch.WordTrace tailWord_2022985 prefixEnd_2022985 1038763661835872795583967 := by
  unfold tailWord_2022985
  simp only [CollatzResearch.WordTrace]
  refine ⟨73784324576078318176582409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49189549717385545451054939 73784324576078318176582409)
  ·
    refine ⟨55338243432058738632436807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73784324576078318176582409 55338243432058738632436807)
    ·
      refine ⟨83007365148088107948655211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55338243432058738632436807 83007365148088107948655211)
      ·
        refine ⟨124511047722132161922982817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83007365148088107948655211 124511047722132161922982817)
        ·
          refine ⟨93383285791599121442237113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124511047722132161922982817 93383285791599121442237113)
          ·
            refine ⟨70037464343699341081677835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93383285791599121442237113 70037464343699341081677835)
            ·
              refine ⟨105056196515549011622516753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70037464343699341081677835 105056196515549011622516753)
              ·
                refine ⟨78792147386661758716887565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105056196515549011622516753 78792147386661758716887565)
                ·
                  refine ⟨29547055269998159518832837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78792147386661758716887565 29547055269998159518832837)
                  ·
                    refine ⟨5540072863124654909781157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29547055269998159518832837 5540072863124654909781157)
                    ·
                      refine ⟨1038763661835872795583967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5540072863124654909781157 1038763661835872795583967)
                      ·
                        rfl

theorem cell23_2022985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_2022985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2022985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2022985 prefixEnd_2022985 := by exact prefixLift 2022985
  have htrace : WordTrace (prefixWord ++ tailWord_2022985) baseStart_2022985 baseEnd_2022985 := by
    simpa [prefixWord, tailWord_2022985, baseEnd_2022985] using wordTrace_append hprefix tailTrace_2022985
  have hstable : (prefixWord ++ tailWord_2022985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022985).length < 2 ^ (prefixWord ++ tailWord_2022985).sum := by decide
  have hdescent : baseEnd_2022985 < baseStart_2022985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023012 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 7]
def baseStart_2023012 : Nat := 118140960795 + 2023012 * 2 ^ 59
def prefixEnd_2023012 : Nat := 4983230072969 + 3 ^ 40 * 2023012 * 2
def baseEnd_2023012 : Nat := 115419725090393798882927

theorem tailTrace_2023012 : CollatzResearch.WordTrace tailWord_2023012 prefixEnd_2023012 115419725090393798882927 := by
  unfold tailWord_2023012
  simp only [CollatzResearch.WordTrace]
  refine ⟨36892654673490250893907645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49190206231320334525210193 36892654673490250893907645)
  ·
    refine ⟨13834745502558844085215367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36892654673490250893907645 13834745502558844085215367)
    ·
      refine ⟨20752118253838266127823051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13834745502558844085215367 20752118253838266127823051)
      ·
        refine ⟨31128177380757399191734577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20752118253838266127823051 31128177380757399191734577)
        ·
          refine ⟨23346133035568049393800933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31128177380757399191734577 23346133035568049393800933)
          ·
            refine ⟨4377399944169009261337675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23346133035568049393800933 4377399944169009261337675)
            ·
              refine ⟨6566099916253513892006513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4377399944169009261337675 6566099916253513892006513)
              ·
                refine ⟨4924574937190135419004885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6566099916253513892006513 4924574937190135419004885)
                ·
                  refine ⟨115419725090393798882927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4924574937190135419004885 115419725090393798882927)
                  ·
                    rfl

theorem cell23_2023012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_2023012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023012 prefixEnd_2023012 := by exact prefixLift 2023012
  have htrace : WordTrace (prefixWord ++ tailWord_2023012) baseStart_2023012 baseEnd_2023012 := by
    simpa [prefixWord, tailWord_2023012, baseEnd_2023012] using wordTrace_append hprefix tailTrace_2023012
  have hstable : (prefixWord ++ tailWord_2023012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023012).length < 2 ^ (prefixWord ++ tailWord_2023012).sum := by decide
  have hdescent : baseEnd_2023012 < baseStart_2023012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023055 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 4, 8]
def baseStart_2023055 : Nat := 118140960795 + 2023055 * 2 ^ 59
def prefixEnd_2023055 : Nat := 4983230072969 + 3 ^ 40 * 2023055 * 2
def baseEnd_2023055 : Nat := 346266535160562507236215

theorem tailTrace_2023055 : CollatzResearch.WordTrace tailWord_2023055 prefixEnd_2023055 346266535160562507236215 := by
  unfold tailWord_2023055
  simp only [CollatzResearch.WordTrace]
  refine ⟨73786877685824720131630619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49191251790549813421087079 73786877685824720131630619)
  ·
    refine ⟨110680316528737080197445929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73786877685824720131630619 110680316528737080197445929)
    ·
      refine ⟨83010237396552810148084447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110680316528737080197445929 83010237396552810148084447)
      ·
        refine ⟨124515356094829215222126671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83010237396552810148084447 124515356094829215222126671)
        ·
          refine ⟨186773034142243822833190007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124515356094829215222126671 186773034142243822833190007)
          ·
            refine ⟨280159551213365734249785011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186773034142243822833190007 280159551213365734249785011)
            ·
              refine ⟨420239326820048601374677517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280159551213365734249785011 420239326820048601374677517)
              ·
                refine ⟨157589747557518225515504069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420239326820048601374677517 157589747557518225515504069)
                ·
                  refine ⟨29548077667034667284157013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157589747557518225515504069 29548077667034667284157013)
                  ·
                    refine ⟨346266535160562507236215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29548077667034667284157013 346266535160562507236215)
                    ·
                      rfl

theorem cell23_2023055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_2023055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023055 prefixEnd_2023055 := by exact prefixLift 2023055
  have htrace : WordTrace (prefixWord ++ tailWord_2023055) baseStart_2023055 baseEnd_2023055 := by
    simpa [prefixWord, tailWord_2023055, baseEnd_2023055] using wordTrace_append hprefix tailTrace_2023055
  have hstable : (prefixWord ++ tailWord_2023055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023055).length < 2 ^ (prefixWord ++ tailWord_2023055).sum := by decide
  have hdescent : baseEnd_2023055 < baseStart_2023055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023162 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_2023162 : Nat := 118140960795 + 2023162 * 2 ^ 59
def prefixEnd_2023162 : Nat := 4983230072969 + 3 ^ 40 * 2023162 * 2
def baseEnd_2023162 : Nat := 346284849303906201023551

theorem tailTrace_2023162 : CollatzResearch.WordTrace tailWord_2023162 prefixEnd_2023162 346284849303906201023551 := by
  unfold tailWord_2023162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18447695074109269351443935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49193853530958051603850493 18447695074109269351443935)
  ·
    refine ⟨27671542611163904027165903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18447695074109269351443935 27671542611163904027165903)
    ·
      refine ⟨41507313916745856040748855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27671542611163904027165903 41507313916745856040748855)
      ·
        refine ⟨62260970875118784061123283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41507313916745856040748855 62260970875118784061123283)
        ·
          refine ⟨93391456312678176091684925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62260970875118784061123283 93391456312678176091684925)
          ·
            refine ⟨35021796117254316034381847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93391456312678176091684925 35021796117254316034381847)
            ·
              refine ⟨52532694175881474051572771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35021796117254316034381847 52532694175881474051572771)
              ·
                refine ⟨78799041263822211077359157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52532694175881474051572771 78799041263822211077359157)
                ·
                  refine ⟨7387410118483332288502421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78799041263822211077359157 7387410118483332288502421)
                  ·
                    refine ⟨346284849303906201023551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7387410118483332288502421 346284849303906201023551)
                    ·
                      rfl

theorem cell23_2023162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_2023162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023162 prefixEnd_2023162 := by exact prefixLift 2023162
  have htrace : WordTrace (prefixWord ++ tailWord_2023162) baseStart_2023162 baseEnd_2023162 := by
    simpa [prefixWord, tailWord_2023162, baseEnd_2023162] using wordTrace_append hprefix tailTrace_2023162
  have hstable : (prefixWord ++ tailWord_2023162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023162).length < 2 ^ (prefixWord ++ tailWord_2023162).sum := by decide
  have hdescent : baseEnd_2023162 < baseStart_2023162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023169 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2023169 : Nat := 118140960795 + 2023169 * 2 ^ 59
def prefixEnd_2023169 : Nat := 4983230072969 + 3 ^ 40 * 2023169 * 2
def baseEnd_2023169 : Nat := 1038858142276300075683121

theorem tailTrace_2023169 : CollatzResearch.WordTrace tailWord_2023169 prefixEnd_2023169 1038858142276300075683121 := by
  unfold tailWord_2023169
  simp only [CollatzResearch.WordTrace]
  refine ⟨73791035607411717601280561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49194023738274478400853707 73791035607411717601280561)
  ·
    refine ⟨55343276705558788200960421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73791035607411717601280561 55343276705558788200960421)
    ·
      refine ⟨10376864382292272787680079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55343276705558788200960421 10376864382292272787680079)
      ·
        refine ⟨15565296573438409181520119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10376864382292272787680079 15565296573438409181520119)
        ·
          refine ⟨23347944860157613772280179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15565296573438409181520119 23347944860157613772280179)
          ·
            refine ⟨35021917290236420658420269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23347944860157613772280179 35021917290236420658420269)
            ·
              refine ⟨13133218983838657746907601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35021917290236420658420269 13133218983838657746907601)
              ·
                refine ⟨9849914237878993310180701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13133218983838657746907601 9849914237878993310180701)
                ·
                  refine ⟨3693717839204622491317763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9849914237878993310180701 3693717839204622491317763)
                  ·
                    refine ⟨5540576758806933736976645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3693717839204622491317763 5540576758806933736976645)
                    ·
                      refine ⟨1038858142276300075683121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5540576758806933736976645 1038858142276300075683121)
                      ·
                        rfl

theorem cell23_2023169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2023169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023169 prefixEnd_2023169 := by exact prefixLift 2023169
  have htrace : WordTrace (prefixWord ++ tailWord_2023169) baseStart_2023169 baseEnd_2023169 := by
    simpa [prefixWord, tailWord_2023169, baseEnd_2023169] using wordTrace_append hprefix tailTrace_2023169
  have hstable : (prefixWord ++ tailWord_2023169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023169).length < 2 ^ (prefixWord ++ tailWord_2023169).sum := by decide
  have hdescent : baseEnd_2023169 < baseStart_2023169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023174 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2023174 : Nat := 118140960795 + 2023174 * 2 ^ 59
def prefixEnd_2023174 : Nat := 4983230072969 + 3 ^ 40 * 2023174 * 2
def baseEnd_2023174 : Nat := 346286903226524185373533

theorem tailTrace_2023174 : CollatzResearch.WordTrace tailWord_2023174 prefixEnd_2023174 346286903226524185373533 := by
  unfold tailWord_2023174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305975561637300107975393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49194145314929068970141717 2305975561637300107975393)
  ·
    refine ⟨1729481671227975080981545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2305975561637300107975393 1729481671227975080981545)
    ·
      refine ⟨1297111253420981310736159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1729481671227975080981545 1297111253420981310736159)
      ·
        refine ⟨1945666880131471966104239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1297111253420981310736159 1945666880131471966104239)
        ·
          refine ⟨2918500320197207949156359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945666880131471966104239 2918500320197207949156359)
          ·
            refine ⟨4377750480295811923734539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918500320197207949156359 4377750480295811923734539)
            ·
              refine ⟨6566625720443717885601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4377750480295811923734539 6566625720443717885601809)
              ·
                refine ⟨4924969290332788414201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6566625720443717885601809 4924969290332788414201357)
                ·
                  refine ⟨1846863483874795655325509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4924969290332788414201357 1846863483874795655325509)
                  ·
                    refine ⟨346286903226524185373533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1846863483874795655325509 346286903226524185373533)
                    ·
                      rfl

theorem cell23_2023174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2023174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023174 prefixEnd_2023174 := by exact prefixLift 2023174
  have htrace : WordTrace (prefixWord ++ tailWord_2023174) baseStart_2023174 baseEnd_2023174 := by
    simpa [prefixWord, tailWord_2023174, baseEnd_2023174] using wordTrace_append hprefix tailTrace_2023174
  have hstable : (prefixWord ++ tailWord_2023174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023174).length < 2 ^ (prefixWord ++ tailWord_2023174).sum := by decide
  have hdescent : baseEnd_2023174 < baseStart_2023174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023192 : List Nat := [2, 1, 2, 3, 1, 1, 2, 11]
def baseStart_2023192 : Nat := 118140960795 + 2023192 * 2 ^ 59
def prefixEnd_2023192 : Nat := 4983230072969 + 3 ^ 40 * 2023192 * 2
def baseEnd_2023192 : Nat := 38476664901161240210945

theorem tailTrace_2023192 : CollatzResearch.WordTrace tailWord_2023192 prefixEnd_2023192 38476664901161240210945 := by
  unfold tailWord_2023192
  simp only [CollatzResearch.WordTrace]
  refine ⟨36895937243164196264683915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49194582990885595019578553 36895937243164196264683915)
  ·
    refine ⟨55343905864746294397025873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36895937243164196264683915 55343905864746294397025873)
    ·
      refine ⟨41507929398559720797769405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55343905864746294397025873 41507929398559720797769405)
      ·
        refine ⟨15565473524459895299163527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41507929398559720797769405 15565473524459895299163527)
        ·
          refine ⟨23348210286689842948745291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15565473524459895299163527 23348210286689842948745291)
          ·
            refine ⟨35022315430034764423117937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23348210286689842948745291 35022315430034764423117937)
            ·
              refine ⟨26266736572526073317338453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35022315430034764423117937 26266736572526073317338453)
              ·
                refine ⟨38476664901161240210945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 26266736572526073317338453 38476664901161240210945)
                ·
                  rfl

theorem cell23_2023192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 11].length) (baseStart_2023192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023192 prefixEnd_2023192 := by exact prefixLift 2023192
  have htrace : WordTrace (prefixWord ++ tailWord_2023192) baseStart_2023192 baseEnd_2023192 := by
    simpa [prefixWord, tailWord_2023192, baseEnd_2023192] using wordTrace_append hprefix tailTrace_2023192
  have hstable : (prefixWord ++ tailWord_2023192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023192).length < 2 ^ (prefixWord ++ tailWord_2023192).sum := by decide
  have hdescent : baseEnd_2023192 < baseStart_2023192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023199 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_2023199 : Nat := 118140960795 + 2023199 * 2 ^ 59
def prefixEnd_2023199 : Nat := 4983230072969 + 3 ^ 40 * 2023199 * 2
def baseEnd_2023199 : Nat := 1038873546695934958307983

theorem tailTrace_2023199 : CollatzResearch.WordTrace tailWord_2023199 prefixEnd_2023199 1038873546695934958307983 := by
  unfold tailWord_2023199
  simp only [CollatzResearch.WordTrace]
  refine ⟨73792129797303032724872651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49194753198202021816581767 73792129797303032724872651)
  ·
    refine ⟨110688194695954549087308977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73792129797303032724872651 110688194695954549087308977)
    ·
      refine ⟨83016146021965911815481733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110688194695954549087308977 83016146021965911815481733)
      ·
        refine ⟨15565527379118608465402825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83016146021965911815481733 15565527379118608465402825)
        ·
          refine ⟨11674145534338956349052119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15565527379118608465402825 11674145534338956349052119)
          ·
            refine ⟨17511218301508434523578179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11674145534338956349052119 17511218301508434523578179)
            ·
              refine ⟨26266827452262651785367269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17511218301508434523578179 26266827452262651785367269)
              ·
                refine ⟨4925030147299247209756363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26266827452262651785367269 4925030147299247209756363)
                ·
                  refine ⟨7387545220948870814634545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925030147299247209756363 7387545220948870814634545)
                  ·
                    refine ⟨5540658915711653110975909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7387545220948870814634545 5540658915711653110975909)
                    ·
                      refine ⟨1038873546695934958307983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5540658915711653110975909 1038873546695934958307983)
                      ·
                        rfl

theorem cell23_2023199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_2023199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023199 prefixEnd_2023199 := by exact prefixLift 2023199
  have htrace : WordTrace (prefixWord ++ tailWord_2023199) baseStart_2023199 baseEnd_2023199 := by
    simpa [prefixWord, tailWord_2023199, baseEnd_2023199] using wordTrace_append hprefix tailTrace_2023199
  have hstable : (prefixWord ++ tailWord_2023199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023199).length < 2 ^ (prefixWord ++ tailWord_2023199).sum := by decide
  have hdescent : baseEnd_2023199 < baseStart_2023199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023220 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2023220 : Nat := 118140960795 + 2023220 * 2 ^ 59
def prefixEnd_2023220 : Nat := 4983230072969 + 3 ^ 40 * 2023220 * 2
def baseEnd_2023220 : Nat := 1038884329789679376145387

theorem tailTrace_2023220 : CollatzResearch.WordTrace tailWord_2023220 prefixEnd_2023220 1038884329789679376145387 := by
  unfold tailWord_2023220
  simp only [CollatzResearch.WordTrace]
  refine ⟨36896447865113476655693557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49195263820151302207591409 36896447865113476655693557)
  ·
    refine ⟨3459041987354388436471271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36896447865113476655693557 3459041987354388436471271)
    ·
      refine ⟨5188562981031582654706907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3459041987354388436471271 5188562981031582654706907)
      ·
        refine ⟨7782844471547373982060361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188562981031582654706907 7782844471547373982060361)
        ·
          refine ⟨5837133353660530486545271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7782844471547373982060361 5837133353660530486545271)
          ·
            refine ⟨8755700030490795729817907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837133353660530486545271 8755700030490795729817907)
            ·
              refine ⟨13133550045736193594726861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755700030490795729817907 13133550045736193594726861)
              ·
                refine ⟨4925081267151072598022573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13133550045736193594726861 4925081267151072598022573)
                ·
                  refine ⟨1846905475181652224258465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4925081267151072598022573 1846905475181652224258465)
                  ·
                    refine ⟨1385179106386239168193849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1846905475181652224258465 1385179106386239168193849)
                    ·
                      refine ⟨1038884329789679376145387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385179106386239168193849 1038884329789679376145387)
                      ·
                        rfl

theorem cell23_2023220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2023220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023220 prefixEnd_2023220 := by exact prefixLift 2023220
  have htrace : WordTrace (prefixWord ++ tailWord_2023220) baseStart_2023220 baseEnd_2023220 := by
    simpa [prefixWord, tailWord_2023220, baseEnd_2023220] using wordTrace_append hprefix tailTrace_2023220
  have hstable : (prefixWord ++ tailWord_2023220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023220).length < 2 ^ (prefixWord ++ tailWord_2023220).sum := by decide
  have hdescent : baseEnd_2023220 < baseStart_2023220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023230 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_2023230 : Nat := 118140960795 + 2023230 * 2 ^ 59
def prefixEnd_2023230 : Nat := 4983230072969 + 3 ^ 40 * 2023230 * 2
def baseEnd_2023230 : Nat := 346296488198741445673447

theorem tailTrace_2023230 : CollatzResearch.WordTrace tailWord_2023230 prefixEnd_2023230 346296488198741445673447 := by
  unfold tailWord_2023230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9224157557523840627406393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49195506973460483346167429 9224157557523840627406393)
  ·
    refine ⟨6918118168142880470554795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9224157557523840627406393 6918118168142880470554795)
    ·
      refine ⟨10377177252214320705832193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6918118168142880470554795 10377177252214320705832193)
      ·
        refine ⟨7782882939160740529374145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10377177252214320705832193 7782882939160740529374145)
        ·
          refine ⟨5837162204370555397030609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7782882939160740529374145 5837162204370555397030609)
          ·
            refine ⟨4377871653277916547772957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5837162204370555397030609 4377871653277916547772957)
            ·
              refine ⟨1641701869979218705414859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4377871653277916547772957 1641701869979218705414859)
              ·
                refine ⟨2462552804968828058122289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641701869979218705414859 2462552804968828058122289)
                ·
                  refine ⟨1846914603726621043591717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2462552804968828058122289 1846914603726621043591717)
                  ·
                    refine ⟨346296488198741445673447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1846914603726621043591717 346296488198741445673447)
                    ·
                      rfl

theorem cell23_2023230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_2023230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023230 prefixEnd_2023230 := by exact prefixLift 2023230
  have htrace : WordTrace (prefixWord ++ tailWord_2023230) baseStart_2023230 baseEnd_2023230 := by
    simpa [prefixWord, tailWord_2023230, baseEnd_2023230] using wordTrace_append hprefix tailTrace_2023230
  have hstable : (prefixWord ++ tailWord_2023230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023230).length < 2 ^ (prefixWord ++ tailWord_2023230).sum := by decide
  have hdescent : baseEnd_2023230 < baseStart_2023230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023249 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_2023249 : Nat := 118140960795 + 2023249 * 2 ^ 59
def prefixEnd_2023249 : Nat := 4983230072969 + 3 ^ 40 * 2023249 * 2
def baseEnd_2023249 : Nat := 1038899220728659762682753

theorem tailTrace_2023249 : CollatzResearch.WordTrace tailWord_2023249 prefixEnd_2023249 1038899220728659762682753 := by
  unfold tailWord_2023249
  simp only [CollatzResearch.WordTrace]
  refine ⟨73793953447121891264192801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49195968964747927509461867 73793953447121891264192801)
  ·
    refine ⟨55345465085341418448144601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73793953447121891264192801 55345465085341418448144601)
    ·
      refine ⟨41509098814006063836108451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55345465085341418448144601 41509098814006063836108451)
      ·
        refine ⟨62263648221009095754162677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41509098814006063836108451 62263648221009095754162677)
        ·
          refine ⟨5837217020719602726952751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62263648221009095754162677 5837217020719602726952751)
          ·
            refine ⟨8755825531079404090429127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837217020719602726952751 8755825531079404090429127)
            ·
              refine ⟨13133738296619106135643691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8755825531079404090429127 13133738296619106135643691)
              ·
                refine ⟨19700607444928659203465537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13133738296619106135643691 19700607444928659203465537)
                ·
                  refine ⟨14775455583696494402599153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19700607444928659203465537 14775455583696494402599153)
                  ·
                    refine ⟨11081591687772370801949365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14775455583696494402599153 11081591687772370801949365)
                    ·
                      refine ⟨1038899220728659762682753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11081591687772370801949365 1038899220728659762682753)
                      ·
                        rfl

theorem cell23_2023249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_2023249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023249 prefixEnd_2023249 := by exact prefixLift 2023249
  have htrace : WordTrace (prefixWord ++ tailWord_2023249) baseStart_2023249 baseEnd_2023249 := by
    simpa [prefixWord, tailWord_2023249, baseEnd_2023249] using wordTrace_append hprefix tailTrace_2023249
  have hstable : (prefixWord ++ tailWord_2023249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023249).length < 2 ^ (prefixWord ++ tailWord_2023249).sum := by decide
  have hdescent : baseEnd_2023249 < baseStart_2023249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023263 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 1, 3, 2]
def baseStart_2023263 : Nat := 118140960795 + 2023263 * 2 ^ 59
def prefixEnd_2023263 : Nat := 4983230072969 + 3 ^ 40 * 2023263 * 2
def baseEnd_2023263 : Nat := 1038906409457822707907689

theorem tailTrace_2023263 : CollatzResearch.WordTrace tailWord_2023263 prefixEnd_2023263 1038906409457822707907689 := by
  unfold tailWord_2023263
  simp only [CollatzResearch.WordTrace]
  refine ⟨73794464069071171655202443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49196309379380781103468295 73794464069071171655202443)
  ·
    refine ⟨110691696103606757482803665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73794464069071171655202443 110691696103606757482803665)
    ·
      refine ⟨83018772077705068112102749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110691696103606757482803665 83018772077705068112102749)
      ·
        refine ⟨31132039529139400542038531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83018772077705068112102749 31132039529139400542038531)
        ·
          refine ⟨46698059293709100813057797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31132039529139400542038531 46698059293709100813057797)
          ·
            refine ⟨8755886117570456402448337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46698059293709100813057797 8755886117570456402448337)
            ·
              refine ⟨6566914588177842301836253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8755886117570456402448337 6566914588177842301836253)
              ·
                refine ⟨2462592970566690863188595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6566914588177842301836253 2462592970566690863188595)
                ·
                  refine ⟨3693889455850036294782893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462592970566690863188595 3693889455850036294782893)
                  ·
                    refine ⟨1385208545943763610543585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3693889455850036294782893 1385208545943763610543585)
                    ·
                      refine ⟨1038906409457822707907689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385208545943763610543585 1038906409457822707907689)
                      ·
                        rfl

theorem cell23_2023263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_2023263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023263 prefixEnd_2023263 := by exact prefixLift 2023263
  have htrace : WordTrace (prefixWord ++ tailWord_2023263) baseStart_2023263 baseEnd_2023263 := by
    simpa [prefixWord, tailWord_2023263, baseEnd_2023263] using wordTrace_append hprefix tailTrace_2023263
  have hstable : (prefixWord ++ tailWord_2023263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023263).length < 2 ^ (prefixWord ++ tailWord_2023263).sum := by decide
  have hdescent : baseEnd_2023263 < baseStart_2023263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023289 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2023289 : Nat := 118140960795 + 2023289 * 2 ^ 59
def prefixEnd_2023289 : Nat := 4983230072969 + 3 ^ 40 * 2023289 * 2
def baseEnd_2023289 : Nat := 1038919759954839606182569

theorem tailTrace_2023289 : CollatzResearch.WordTrace tailWord_2023289 prefixEnd_2023289 1038919759954839606182569 := by
  unfold tailWord_2023289
  simp only [CollatzResearch.WordTrace]
  refine ⟨73795412366976978095648921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49196941577984652063765947 73795412366976978095648921)
  ·
    refine ⟨55346559275232733571736691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73795412366976978095648921 55346559275232733571736691)
    ·
      refine ⟨83019838912849100357605037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55346559275232733571736691 83019838912849100357605037)
      ·
        refine ⟨31132439592318412634101889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83019838912849100357605037 31132439592318412634101889)
        ·
          refine ⟨23349329694238809475576417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31132439592318412634101889 23349329694238809475576417)
          ·
            refine ⟨17511997270679107106682313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23349329694238809475576417 17511997270679107106682313)
            ·
              refine ⟨13133997953009330330011735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17511997270679107106682313 13133997953009330330011735)
              ·
                refine ⟨19700996929513995495017603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13133997953009330330011735 19700996929513995495017603)
                ·
                  refine ⟨29551495394270993242526405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19700996929513995495017603 29551495394270993242526405)
                  ·
                    refine ⟨5540905386425811232973701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29551495394270993242526405 5540905386425811232973701)
                    ·
                      refine ⟨1038919759954839606182569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5540905386425811232973701 1038919759954839606182569)
                      ·
                        rfl

theorem cell23_2023289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2023289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023289 prefixEnd_2023289 := by exact prefixLift 2023289
  have htrace : WordTrace (prefixWord ++ tailWord_2023289) baseStart_2023289 baseEnd_2023289 := by
    simpa [prefixWord, tailWord_2023289, baseEnd_2023289] using wordTrace_append hprefix tailTrace_2023289
  have hstable : (prefixWord ++ tailWord_2023289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023289).length < 2 ^ (prefixWord ++ tailWord_2023289).sum := by decide
  have hdescent : baseEnd_2023289 < baseStart_2023289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023327 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 2, 2, 2]
def baseStart_2023327 : Nat := 118140960795 + 2023327 * 2 ^ 59
def prefixEnd_2023327 : Nat := 4983230072969 + 3 ^ 40 * 2023327 * 2
def baseEnd_2023327 : Nat := 1038939272219710457507395

theorem tailTrace_2023327 : CollatzResearch.WordTrace tailWord_2023327 prefixEnd_2023327 1038939272219710457507395 := by
  unfold tailWord_2023327
  simp only [CollatzResearch.WordTrace]
  refine ⟨73796798340839310585532235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49197865560559540390354823 73796798340839310585532235)
  ·
    refine ⟨110695197511258965878298353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73796798340839310585532235 110695197511258965878298353)
    ·
      refine ⟨83021398133444224408723765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110695197511258965878298353 83021398133444224408723765)
      ·
        refine ⟨7783256075010396038317853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83021398133444224408723765 7783256075010396038317853)
        ·
          refine ⟨2918721028128898514369195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7783256075010396038317853 2918721028128898514369195)
          ·
            refine ⟨4378081542193347771553793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918721028128898514369195 4378081542193347771553793)
            ·
              refine ⟨3283561156645010828665345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4378081542193347771553793 3283561156645010828665345)
              ·
                refine ⟨2462670867483758121499009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283561156645010828665345 2462670867483758121499009)
                ·
                  refine ⟨1847003150612818591124257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2462670867483758121499009 1847003150612818591124257)
                  ·
                    refine ⟨1385252362959613943343193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1847003150612818591124257 1385252362959613943343193)
                    ·
                      refine ⟨1038939272219710457507395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385252362959613943343193 1038939272219710457507395)
                      ·
                        rfl

theorem cell23_2023327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_2023327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023327 prefixEnd_2023327 := by exact prefixLift 2023327
  have htrace : WordTrace (prefixWord ++ tailWord_2023327) baseStart_2023327 baseEnd_2023327 := by
    simpa [prefixWord, tailWord_2023327, baseEnd_2023327] using wordTrace_append hprefix tailTrace_2023327
  have hstable : (prefixWord ++ tailWord_2023327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023327).length < 2 ^ (prefixWord ++ tailWord_2023327).sum := by decide
  have hdescent : baseEnd_2023327 < baseStart_2023327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023443 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 4, 3, 2]
def baseStart_2023443 : Nat := 118140960795 + 2023443 * 2 ^ 59
def prefixEnd_2023443 : Nat := 4983230072969 + 3 ^ 40 * 2023443 * 2
def baseEnd_2023443 : Nat := 1038998835975632003656861

theorem tailTrace_2023443 : CollatzResearch.WordTrace tailWord_2023443 prefixEnd_2023443 1038998835975632003656861 := by
  unfold tailWord_2023443
  simp only [CollatzResearch.WordTrace]
  refine ⟨73801029208419062396754983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49200686138946041597836655 73801029208419062396754983)
  ·
    refine ⟨110701543812628593595132475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73801029208419062396754983 110701543812628593595132475)
    ·
      refine ⟨166052315718942890392698713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110701543812628593595132475 166052315718942890392698713)
      ·
        refine ⟨124539236789207167794524035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166052315718942890392698713 124539236789207167794524035)
        ·
          refine ⟨186808855183810751691786053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124539236789207167794524035 186808855183810751691786053)
          ·
            refine ⟨35026660346964515942209885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186808855183810751691786053 35026660346964515942209885)
            ·
              refine ⟨13134997630111693478328707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35026660346964515942209885 13134997630111693478328707)
              ·
                refine ⟨19702496445167540217493061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134997630111693478328707 19702496445167540217493061)
                ·
                  refine ⟨3694218083468913790779949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19702496445167540217493061 3694218083468913790779949)
                  ·
                    refine ⟨1385331781300842671542481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3694218083468913790779949 1385331781300842671542481)
                    ·
                      refine ⟨1038998835975632003656861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385331781300842671542481 1038998835975632003656861)
                      ·
                        rfl

theorem cell23_2023443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3, 2].length) (baseStart_2023443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023443 prefixEnd_2023443 := by exact prefixLift 2023443
  have htrace : WordTrace (prefixWord ++ tailWord_2023443) baseStart_2023443 baseEnd_2023443 := by
    simpa [prefixWord, tailWord_2023443, baseEnd_2023443] using wordTrace_append hprefix tailTrace_2023443
  have hstable : (prefixWord ++ tailWord_2023443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023443).length < 2 ^ (prefixWord ++ tailWord_2023443).sum := by decide
  have hdescent : baseEnd_2023443 < baseStart_2023443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023444 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2023444 : Nat := 118140960795 + 2023444 * 2 ^ 59
def prefixEnd_2023444 : Nat := 4983230072969 + 3 ^ 40 * 2023444 * 2
def baseEnd_2023444 : Nat := 346333116485428833248119

theorem tailTrace_2023444 : CollatzResearch.WordTrace tailWord_2023444 prefixEnd_2023444 346333116485428833248119 := by
  unfold tailWord_2023444
  simp only [CollatzResearch.WordTrace]
  refine ⟨36900532840707719783770693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49200710454276959711694257 36900532840707719783770693)
  ·
    refine ⟨6918849907632697459457005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36900532840707719783770693 6918849907632697459457005)
    ·
      refine ⟨2594568715362261547296377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6918849907632697459457005 2594568715362261547296377)
      ·
        refine ⟨1945926536521696160472283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2594568715362261547296377 1945926536521696160472283)
        ·
          refine ⟨2918889804782544240708425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945926536521696160472283 2918889804782544240708425)
          ·
            refine ⟨2189167353586908180531319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2918889804782544240708425 2189167353586908180531319)
            ·
              refine ⟨3283751030380362270796979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189167353586908180531319 3283751030380362270796979)
              ·
                refine ⟨4925626545570543406195469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283751030380362270796979 4925626545570543406195469)
                ·
                  refine ⟨1847109954588953777323301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4925626545570543406195469 1847109954588953777323301)
                  ·
                    refine ⟨346333116485428833248119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847109954588953777323301 346333116485428833248119)
                    ·
                      rfl

theorem cell23_2023444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2023444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023444 prefixEnd_2023444 := by exact prefixLift 2023444
  have htrace : WordTrace (prefixWord ++ tailWord_2023444) baseStart_2023444 baseEnd_2023444 := by
    simpa [prefixWord, tailWord_2023444, baseEnd_2023444] using wordTrace_append hprefix tailTrace_2023444
  have hstable : (prefixWord ++ tailWord_2023444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023444).length < 2 ^ (prefixWord ++ tailWord_2023444).sum := by decide
  have hdescent : baseEnd_2023444 < baseStart_2023444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023450 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_2023450 : Nat := 118140960795 + 2023450 * 2 ^ 59
def prefixEnd_2023450 : Nat := 4983230072969 + 3 ^ 40 * 2023450 * 2
def baseEnd_2023450 : Nat := 1039002430340213476269329

theorem tailTrace_2023450 : CollatzResearch.WordTrace tailWord_2023450 prefixEnd_2023450 1039002430340213476269329 := by
  unfold tailWord_2023450
  simp only [CollatzResearch.WordTrace]
  refine ⟨18450321129848425648064951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49200856346262468394839869 18450321129848425648064951)
  ·
    refine ⟨27675481694772638472097427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18450321129848425648064951 27675481694772638472097427)
    ·
      refine ⟨41513222542158957708146141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27675481694772638472097427 41513222542158957708146141)
      ·
        refine ⟨15567458453309609140554803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41513222542158957708146141 15567458453309609140554803)
        ·
          refine ⟨23351187679964413710832205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15567458453309609140554803 23351187679964413710832205)
          ·
            refine ⟨8756695379986655141562077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23351187679964413710832205 8756695379986655141562077)
            ·
              refine ⟨3283760767494995678085779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8756695379986655141562077 3283760767494995678085779)
              ·
                refine ⟨4925641151242493517128669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283760767494995678085779 4925641151242493517128669)
                ·
                  refine ⟨1847115431715935068923251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4925641151242493517128669 1847115431715935068923251)
                  ·
                    refine ⟨2770673147573902603384877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1847115431715935068923251 2770673147573902603384877)
                    ·
                      refine ⟨1039002430340213476269329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2770673147573902603384877 1039002430340213476269329)
                      ·
                        rfl

theorem cell23_2023450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_2023450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023450 prefixEnd_2023450 := by exact prefixLift 2023450
  have htrace : WordTrace (prefixWord ++ tailWord_2023450) baseStart_2023450 baseEnd_2023450 := by
    simpa [prefixWord, tailWord_2023450, baseEnd_2023450] using wordTrace_append hprefix tailTrace_2023450
  have hstable : (prefixWord ++ tailWord_2023450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023450).length < 2 ^ (prefixWord ++ tailWord_2023450).sum := by decide
  have hdescent : baseEnd_2023450 < baseStart_2023450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023457 : List Nat := [1, 2, 3, 2, 5, 1, 2, 1, 6]
def baseStart_2023457 : Nat := 118140960795 + 2023457 * 2 ^ 59
def prefixEnd_2023457 : Nat := 4983230072969 + 3 ^ 40 * 2023457 * 2
def baseEnd_2023457 : Nat := 115445113856088327653533

theorem tailTrace_2023457 : CollatzResearch.WordTrace tailWord_2023457 prefixEnd_2023457 115445113856088327653533 := by
  unfold tailWord_2023457
  simp only [CollatzResearch.WordTrace]
  refine ⟨73801539830368342787764625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49201026553578895191843083 73801539830368342787764625)
  ·
    refine ⟨55351154872776257090823469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73801539830368342787764625 55351154872776257090823469)
    ·
      refine ⟨20756683077291096409058801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55351154872776257090823469 20756683077291096409058801)
      ·
        refine ⟨15567512307968322306794101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20756683077291096409058801 15567512307968322306794101)
        ·
          refine ⟨1459454278872030216261947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15567512307968322306794101 1459454278872030216261947)
          ·
            refine ⟨2189181418308045324392921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459454278872030216261947 2189181418308045324392921)
            ·
              refine ⟨1641886063731033993294691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189181418308045324392921 1641886063731033993294691)
              ·
                refine ⟨2462829095596550989942037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641886063731033993294691 2462829095596550989942037)
                ·
                  refine ⟨115445113856088327653533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2462829095596550989942037 115445113856088327653533)
                  ·
                    rfl

theorem cell23_2023457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 1, 6].length) (baseStart_2023457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023457 prefixEnd_2023457 := by exact prefixLift 2023457
  have htrace : WordTrace (prefixWord ++ tailWord_2023457) baseStart_2023457 baseEnd_2023457 := by
    simpa [prefixWord, tailWord_2023457, baseEnd_2023457] using wordTrace_append hprefix tailTrace_2023457
  have hstable : (prefixWord ++ tailWord_2023457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023457).length < 2 ^ (prefixWord ++ tailWord_2023457).sum := by decide
  have hdescent : baseEnd_2023457 < baseStart_2023457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023470 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2023470 : Nat := 118140960795 + 2023470 * 2 ^ 59
def prefixEnd_2023470 : Nat := 4983230072969 + 3 ^ 40 * 2023470 * 2
def baseEnd_2023470 : Nat := 346337566651101132673079

theorem tailTrace_2023470 : CollatzResearch.WordTrace tailWord_2023470 prefixEnd_2023470 346337566651101132673079 := by
  unfold tailWord_2023470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9225251747415155750998483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49201342652880830671991909 9225251747415155750998483)
  ·
    refine ⟨13837877621122733626497725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9225251747415155750998483 13837877621122733626497725)
    ·
      refine ⟨5189204107921025109936647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13837877621122733626497725 5189204107921025109936647)
      ·
        refine ⟨7783806161881537664904971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5189204107921025109936647 7783806161881537664904971)
        ·
          refine ⟨11675709242822306497357457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7783806161881537664904971 11675709242822306497357457)
          ·
            refine ⟨8756781932116729873018093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11675709242822306497357457 8756781932116729873018093)
            ·
              refine ⟨3283793224543773702381785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8756781932116729873018093 3283793224543773702381785)
              ·
                refine ⟨2462844918407830276786339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283793224543773702381785 2462844918407830276786339)
                ·
                  refine ⟨3694267377611745415179509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462844918407830276786339 3694267377611745415179509)
                  ·
                    refine ⟨346337566651101132673079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3694267377611745415179509 346337566651101132673079)
                    ·
                      rfl

theorem cell23_2023470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2023470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023470 prefixEnd_2023470 := by exact prefixLift 2023470
  have htrace : WordTrace (prefixWord ++ tailWord_2023470) baseStart_2023470 baseEnd_2023470 := by
    simpa [prefixWord, tailWord_2023470, baseEnd_2023470] using wordTrace_append hprefix tailTrace_2023470
  have hstable : (prefixWord ++ tailWord_2023470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023470).length < 2 ^ (prefixWord ++ tailWord_2023470).sum := by decide
  have hdescent : baseEnd_2023470 < baseStart_2023470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023473 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_2023473 : Nat := 118140960795 + 2023473 * 2 ^ 59
def prefixEnd_2023473 : Nat := 4983230072969 + 3 ^ 40 * 2023473 * 2
def baseEnd_2023473 : Nat := 1039014240395266886281723

theorem tailTrace_2023473 : CollatzResearch.WordTrace tailWord_2023473 prefixEnd_2023473 1039014240395266886281723 := by
  unfold tailWord_2023473
  simp only [CollatzResearch.WordTrace]
  refine ⟨73802123398310377520347073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49201415598873585013564715 73802123398310377520347073)
  ·
    refine ⟨55351592548732783140260305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73802123398310377520347073 55351592548732783140260305)
    ·
      refine ⟨41513694411549587355195229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55351592548732783140260305 41513694411549587355195229)
      ·
        refine ⟨15567635404331095258198211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41513694411549587355195229 15567635404331095258198211)
        ·
          refine ⟨23351453106496642887297317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15567635404331095258198211 23351453106496642887297317)
          ·
            refine ⟨4378397457468120541368247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23351453106496642887297317 4378397457468120541368247)
            ·
              refine ⟨6567596186202180812052371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4378397457468120541368247 6567596186202180812052371)
              ·
                refine ⟨9851394279303271218078557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6567596186202180812052371 9851394279303271218078557)
                ·
                  refine ⟨3694272854738726706779459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9851394279303271218078557 3694272854738726706779459)
                  ·
                    refine ⟨5541409282108090060169189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3694272854738726706779459 5541409282108090060169189)
                    ·
                      refine ⟨1039014240395266886281723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5541409282108090060169189 1039014240395266886281723)
                      ·
                        rfl

theorem cell23_2023473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_2023473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023473 prefixEnd_2023473 := by exact prefixLift 2023473
  have htrace : WordTrace (prefixWord ++ tailWord_2023473) baseStart_2023473 baseEnd_2023473 := by
    simpa [prefixWord, tailWord_2023473, baseEnd_2023473] using wordTrace_append hprefix tailTrace_2023473
  have hstable : (prefixWord ++ tailWord_2023473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023473).length < 2 ^ (prefixWord ++ tailWord_2023473).sum := by decide
  have hdescent : baseEnd_2023473 < baseStart_2023473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023517 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2023517 : Nat := 118140960795 + 2023517 * 2 ^ 59
def prefixEnd_2023517 : Nat := 4983230072969 + 3 ^ 40 * 2023517 * 2
def baseEnd_2023517 : Nat := 346345611181354904710507

theorem tailTrace_2023517 : CollatzResearch.WordTrace tailWord_2023517 prefixEnd_2023517 346345611181354904710507 := by
  unfold tailWord_2023517
  simp only [CollatzResearch.WordTrace]
  refine ⟨73803728210150973034948805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49202485473433982023299203 73803728210150973034948805)
  ·
    refine ⟨13838199039403307444052901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73803728210150973034948805 13838199039403307444052901)
    ·
      refine ⟨2594662319888120145759919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13838199039403307444052901 2594662319888120145759919)
      ·
        refine ⟨3891993479832180218639879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594662319888120145759919 3891993479832180218639879)
        ·
          refine ⟨5837990219748270327959819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891993479832180218639879 5837990219748270327959819)
          ·
            refine ⟨8756985329622405491939729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837990219748270327959819 8756985329622405491939729)
            ·
              refine ⟨6567738997216804118954797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8756985329622405491939729 6567738997216804118954797)
              ·
                refine ⟨2462902123956301544608049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6567738997216804118954797 2462902123956301544608049)
                ·
                  refine ⟨1847176592967226158456037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2462902123956301544608049 1847176592967226158456037)
                  ·
                    refine ⟨346345611181354904710507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847176592967226158456037 346345611181354904710507)
                    ·
                      rfl

theorem cell23_2023517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2023517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023517 prefixEnd_2023517 := by exact prefixLift 2023517
  have htrace : WordTrace (prefixWord ++ tailWord_2023517) baseStart_2023517 baseEnd_2023517 := by
    simpa [prefixWord, tailWord_2023517, baseEnd_2023517] using wordTrace_append hprefix tailTrace_2023517
  have hstable : (prefixWord ++ tailWord_2023517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023517).length < 2 ^ (prefixWord ++ tailWord_2023517).sum := by decide
  have hdescent : baseEnd_2023517 < baseStart_2023517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023523 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 3]
def baseStart_2023523 : Nat := 118140960795 + 2023523 * 2 ^ 59
def prefixEnd_2023523 : Nat := 4983230072969 + 3 ^ 40 * 2023523 * 2
def baseEnd_2023523 : Nat := 1039039914427991690656493

theorem tailTrace_2023523 : CollatzResearch.WordTrace tailWord_2023523 prefixEnd_2023523 1039039914427991690656493 := by
  unfold tailWord_2023523
  simp only [CollatzResearch.WordTrace]
  refine ⟨73803947048129236059667223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49202631365419490706444815 73803947048129236059667223)
  ·
    refine ⟨110705920572193854089500835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73803947048129236059667223 110705920572193854089500835)
    ·
      refine ⟨166058880858290781134251253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110705920572193854089500835 166058880858290781134251253)
      ·
        refine ⟨15568020080464760731336055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166058880858290781134251253 15568020080464760731336055)
        ·
          refine ⟨23352030120697141097004083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15568020080464760731336055 23352030120697141097004083)
          ·
            refine ⟨35028045181045711645506125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23352030120697141097004083 35028045181045711645506125)
            ·
              refine ⟨13135516942892141867064797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35028045181045711645506125 13135516942892141867064797)
              ·
                refine ⟨4925818853584553200149299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13135516942892141867064797 4925818853584553200149299)
                ·
                  refine ⟨7388728280376829800223949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925818853584553200149299 7388728280376829800223949)
                  ·
                    refine ⟨2770773105141311175083981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7388728280376829800223949 2770773105141311175083981)
                    ·
                      refine ⟨1039039914427991690656493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2770773105141311175083981 1039039914427991690656493)
                      ·
                        rfl

theorem cell23_2023523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_2023523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023523 prefixEnd_2023523 := by exact prefixLift 2023523
  have htrace : WordTrace (prefixWord ++ tailWord_2023523) baseStart_2023523 baseEnd_2023523 := by
    simpa [prefixWord, tailWord_2023523, baseEnd_2023523] using wordTrace_append hprefix tailTrace_2023523
  have hstable : (prefixWord ++ tailWord_2023523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023523).length < 2 ^ (prefixWord ++ tailWord_2023523).sum := by decide
  have hdescent : baseEnd_2023523 < baseStart_2023523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023530 : List Nat := [3, 1, 3, 2, 3, 1, 3, 7]
def baseStart_2023530 : Nat := 118140960795 + 2023530 * 2 ^ 59
def prefixEnd_2023530 : Nat := 4983230072969 + 3 ^ 40 * 2023530 * 2
def baseEnd_2023530 : Nat := 38483092918243450491443

theorem tailTrace_2023530 : CollatzResearch.WordTrace tailWord_2023530 prefixEnd_2023530 38483092918243450491443 := by
  unfold tailWord_2023530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18451050589775969063793011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49202801572735917503448029 18451050589775969063793011)
  ·
    refine ⟨27676575884663953595689517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18451050589775969063793011 27676575884663953595689517)
    ·
      refine ⟨10378715956748982598383569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27676575884663953595689517 10378715956748982598383569)
      ·
        refine ⟨7784036967561736948787677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10378715956748982598383569 7784036967561736948787677)
        ·
          refine ⟨2919013862835651355795379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7784036967561736948787677 2919013862835651355795379)
          ·
            refine ⟨4378520794253477033693069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919013862835651355795379 4378520794253477033693069)
            ·
              refine ⟨1641945297845053887634901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4378520794253477033693069 1641945297845053887634901)
              ·
                refine ⟨38483092918243450491443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1641945297845053887634901 38483092918243450491443)
                ·
                  rfl

theorem cell23_2023530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_2023530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023530 prefixEnd_2023530 := by exact prefixLift 2023530
  have htrace : WordTrace (prefixWord ++ tailWord_2023530) baseStart_2023530 baseEnd_2023530 := by
    simpa [prefixWord, tailWord_2023530, baseEnd_2023530] using wordTrace_append hprefix tailTrace_2023530
  have hstable : (prefixWord ++ tailWord_2023530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023530).length < 2 ^ (prefixWord ++ tailWord_2023530).sum := by decide
  have hdescent : baseEnd_2023530 < baseStart_2023530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023557 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_2023557 : Nat := 118140960795 + 2023557 * 2 ^ 59
def prefixEnd_2023557 : Nat := 4983230072969 + 3 ^ 40 * 2023557 * 2
def baseEnd_2023557 : Nat := 1039057372770244557631337

theorem tailTrace_2023557 : CollatzResearch.WordTrace tailWord_2023557 prefixEnd_2023557 1039057372770244557631337 := by
  unfold tailWord_2023557
  simp only [CollatzResearch.WordTrace]
  refine ⟨73805187130006059866404925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49203458086670706577603283 73805187130006059866404925)
  ·
    refine ⟨27676945173752272449901847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73805187130006059866404925 27676945173752272449901847)
    ·
      refine ⟨41515417760628408674852771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27676945173752272449901847 41515417760628408674852771)
      ·
        refine ⟨62273126640942613012279157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41515417760628408674852771 62273126640942613012279157)
        ·
          refine ⟨5838105622588369969901171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62273126640942613012279157 5838105622588369969901171)
          ·
            refine ⟨8757158433882554954851757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838105622588369969901171 8757158433882554954851757)
            ·
              refine ⟨3283934412705958108069409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8757158433882554954851757 3283934412705958108069409)
              ·
                refine ⟨2462950809529468581052057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3283934412705958108069409 2462950809529468581052057)
                ·
                  refine ⟨1847213107147101435789043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2462950809529468581052057 1847213107147101435789043)
                  ·
                    refine ⟨2770819660720652153683565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1847213107147101435789043 2770819660720652153683565)
                    ·
                      refine ⟨1039057372770244557631337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2770819660720652153683565 1039057372770244557631337)
                      ·
                        rfl

theorem cell23_2023557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_2023557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023557 prefixEnd_2023557 := by exact prefixLift 2023557
  have htrace : WordTrace (prefixWord ++ tailWord_2023557) baseStart_2023557 baseEnd_2023557 := by
    simpa [prefixWord, tailWord_2023557, baseEnd_2023557] using wordTrace_append hprefix tailTrace_2023557
  have hstable : (prefixWord ++ tailWord_2023557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023557).length < 2 ^ (prefixWord ++ tailWord_2023557).sum := by decide
  have hdescent : baseEnd_2023557 < baseStart_2023557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023563 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 8, 2]
def baseStart_2023563 : Nat := 118140960795 + 2023563 * 2 ^ 59
def prefixEnd_2023563 : Nat := 4983230072969 + 3 ^ 40 * 2023563 * 2
def baseEnd_2023563 : Nat := 1039060453654171534156309

theorem tailTrace_2023563 : CollatzResearch.WordTrace tailWord_2023563 prefixEnd_2023563 1039060453654171534156309 := by
  unfold tailWord_2023563
  simp only [CollatzResearch.WordTrace]
  refine ⟨73805405967984322891123343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49203603978656215260748895 73805405967984322891123343)
  ·
    refine ⟨110708108951976484336685015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73805405967984322891123343 110708108951976484336685015)
    ·
      refine ⟨166062163427964726505027523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110708108951976484336685015 166062163427964726505027523)
      ·
        refine ⟨249093245141947089757541285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166062163427964726505027523 249093245141947089757541285)
        ·
          refine ⟨46704983464115079329538991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249093245141947089757541285 46704983464115079329538991)
          ·
            refine ⟨70057475196172618994308487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46704983464115079329538991 70057475196172618994308487)
            ·
              refine ⟨105086212794258928491462731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70057475196172618994308487 105086212794258928491462731)
              ·
                refine ⟨157629319191388392737194097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105086212794258928491462731 157629319191388392737194097)
                ·
                  refine ⟨118221989393541294552895573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157629319191388392737194097 118221989393541294552895573)
                  ·
                    refine ⟨1385413938205562045541745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118221989393541294552895573 1385413938205562045541745)
                    ·
                      refine ⟨1039060453654171534156309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385413938205562045541745 1039060453654171534156309)
                      ·
                        rfl

theorem cell23_2023563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8, 2].length) (baseStart_2023563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023563 prefixEnd_2023563 := by exact prefixLift 2023563
  have htrace : WordTrace (prefixWord ++ tailWord_2023563) baseStart_2023563 baseEnd_2023563 := by
    simpa [prefixWord, tailWord_2023563, baseEnd_2023563] using wordTrace_append hprefix tailTrace_2023563
  have hstable : (prefixWord ++ tailWord_2023563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023563).length < 2 ^ (prefixWord ++ tailWord_2023563).sum := by decide
  have hdescent : baseEnd_2023563 < baseStart_2023563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023620 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 7]
def baseStart_2023620 : Nat := 118140960795 + 2023620 * 2 ^ 59
def prefixEnd_2023620 : Nat := 4983230072969 + 3 ^ 40 * 2023620 * 2
def baseEnd_2023620 : Nat := 115454413561275312349283

theorem tailTrace_2023620 : CollatzResearch.WordTrace tailWord_2023620 prefixEnd_2023620 115454413561275312349283 := by
  unfold tailWord_2023620
  simp only [CollatzResearch.WordTrace]
  refine ⟨36903742464388910812974157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49204989952518547750632209 36903742464388910812974157)
  ·
    refine ⟨13838903424145841554865309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36903742464388910812974157 13838903424145841554865309)
    ·
      refine ⟨5189588784054690583074491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13838903424145841554865309 5189588784054690583074491)
      ·
        refine ⟨7784383176082035874611737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5189588784054690583074491 7784383176082035874611737)
        ·
          refine ⟨5838287382061526905958803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7784383176082035874611737 5838287382061526905958803)
          ·
            refine ⟨8757431073092290358938205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838287382061526905958803 8757431073092290358938205)
            ·
              refine ⟨3284036652409608884601827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8757431073092290358938205 3284036652409608884601827)
              ·
                refine ⟨4926054978614413326902741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284036652409608884601827 4926054978614413326902741)
                ·
                  refine ⟨115454413561275312349283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4926054978614413326902741 115454413561275312349283)
                  ·
                    rfl

theorem cell23_2023620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_2023620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023620 prefixEnd_2023620 := by exact prefixLift 2023620
  have htrace : WordTrace (prefixWord ++ tailWord_2023620) baseStart_2023620 baseEnd_2023620 := by
    simpa [prefixWord, tailWord_2023620, baseEnd_2023620] using wordTrace_append hprefix tailTrace_2023620
  have hstable : (prefixWord ++ tailWord_2023620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023620).length < 2 ^ (prefixWord ++ tailWord_2023620).sum := by decide
  have hdescent : baseEnd_2023620 < baseStart_2023620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023690 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2023690 : Nat := 118140960795 + 2023690 * 2 ^ 59
def prefixEnd_2023690 : Nat := 4983230072969 + 3 ^ 40 * 2023690 * 2
def baseEnd_2023690 : Nat := 1039125665697292537268225

theorem tailTrace_2023690 : CollatzResearch.WordTrace tailWord_2023690 prefixEnd_2023690 1039125665697292537268225 := by
  unfold tailWord_2023690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18452509509631055895249131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49206692025682815720664349 18452509509631055895249131)
  ·
    refine ⟨27678764264446583842873697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18452509509631055895249131 27678764264446583842873697)
    ·
      refine ⟨20759073198334937882155273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27678764264446583842873697 20759073198334937882155273)
      ·
        refine ⟨15569304898751203411616455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20759073198334937882155273 15569304898751203411616455)
        ·
          refine ⟨23353957348126805117424683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15569304898751203411616455 23353957348126805117424683)
          ·
            refine ⟨35030936022190207676137025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23353957348126805117424683 35030936022190207676137025)
            ·
              refine ⟨26273202016642655757102769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35030936022190207676137025 26273202016642655757102769)
              ·
                refine ⟨19704901512481991817827077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26273202016642655757102769 19704901512481991817827077)
                ·
                  refine ⟨3694669033590373465842577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19704901512481991817827077 3694669033590373465842577)
                  ·
                    refine ⟨2771001775192780099381933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3694669033590373465842577 2771001775192780099381933)
                    ·
                      refine ⟨1039125665697292537268225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2771001775192780099381933 1039125665697292537268225)
                      ·
                        rfl

theorem cell23_2023690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2023690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023690 prefixEnd_2023690 := by exact prefixLift 2023690
  have htrace : WordTrace (prefixWord ++ tailWord_2023690) baseStart_2023690 baseEnd_2023690 := by
    simpa [prefixWord, tailWord_2023690, baseEnd_2023690] using wordTrace_append hprefix tailTrace_2023690
  have hstable : (prefixWord ++ tailWord_2023690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023690).length < 2 ^ (prefixWord ++ tailWord_2023690).sum := by decide
  have hdescent : baseEnd_2023690 < baseStart_2023690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023714 : List Nat := [3, 3, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2023714 : Nat := 118140960795 + 2023714 * 2 ^ 59
def prefixEnd_2023714 : Nat := 4983230072969 + 3 ^ 40 * 2023714 * 2
def baseEnd_2023714 : Nat := 346379329744333481122705

theorem tailTrace_2023714 : CollatzResearch.WordTrace tailWord_2023714 prefixEnd_2023714 346379329744333481122705 := by
  unfold tailWord_2023714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18452728347609318919967549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49207275593624850453246797 18452728347609318919967549)
  ·
    refine ⟨6919773130353494594987831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18452728347609318919967549 6919773130353494594987831)
    ·
      refine ⟨10379659695530241892481747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6919773130353494594987831 10379659695530241892481747)
      ·
        refine ⟨15569489543295362838722621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10379659695530241892481747 15569489543295362838722621)
        ·
          refine ⟨5838558578735761064520983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15569489543295362838722621 5838558578735761064520983)
          ·
            refine ⟨8757837868103641596781475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838558578735761064520983 8757837868103641596781475)
            ·
              refine ⟨13136756802155462395172213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8757837868103641596781475 13136756802155462395172213)
              ·
                refine ⟨1231570950202074599547395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13136756802155462395172213 1231570950202074599547395)
                ·
                  refine ⟨1847356425303111899321093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231570950202074599547395 1847356425303111899321093)
                  ·
                    refine ⟨346379329744333481122705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847356425303111899321093 346379329744333481122705)
                    ·
                      rfl

theorem cell23_2023714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2023714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023714 prefixEnd_2023714 := by exact prefixLift 2023714
  have htrace : WordTrace (prefixWord ++ tailWord_2023714) baseStart_2023714 baseEnd_2023714 := by
    simpa [prefixWord, tailWord_2023714, baseEnd_2023714] using wordTrace_append hprefix tailTrace_2023714
  have hstable : (prefixWord ++ tailWord_2023714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023714).length < 2 ^ (prefixWord ++ tailWord_2023714).sum := by decide
  have hdescent : baseEnd_2023714 < baseStart_2023714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023788 : List Nat := [2, 2, 1, 1, 6, 1, 3, 2, 1, 1, 3]
def baseStart_2023788 : Nat := 118140960795 + 2023788 * 2 ^ 59
def prefixEnd_2023788 : Nat := 4983230072969 + 3 ^ 40 * 2023788 * 2
def baseEnd_2023788 : Nat := 1039175986801433153842775

theorem tailTrace_2023788 : CollatzResearch.WordTrace tailWord_2023788 prefixEnd_2023788 1039175986801433153842775 := by
  unfold tailWord_2023788
  simp only [CollatzResearch.WordTrace]
  refine ⟨36906806196084593159032009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49209074928112790878709345 36906806196084593159032009)
  ·
    refine ⟨27680104647063444869274007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36906806196084593159032009 27680104647063444869274007)
    ·
      refine ⟨41520156970595167303911011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27680104647063444869274007 41520156970595167303911011)
      ·
        refine ⟨62280235455892750955866517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41520156970595167303911011 62280235455892750955866517)
        ·
          refine ⟨2919386036994972701056243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62280235455892750955866517 2919386036994972701056243)
          ·
            refine ⟨4379079055492459051584365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919386036994972701056243 4379079055492459051584365)
            ·
              refine ⟨1642154645809672144344137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4379079055492459051584365 1642154645809672144344137)
              ·
                refine ⟨1231615984357254108258103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642154645809672144344137 1231615984357254108258103)
                ·
                  refine ⟨1847423976535881162387155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231615984357254108258103 1847423976535881162387155)
                  ·
                    refine ⟨2771135964803821743580733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1847423976535881162387155 2771135964803821743580733)
                    ·
                      refine ⟨1039175986801433153842775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2771135964803821743580733 1039175986801433153842775)
                      ·
                        rfl

theorem cell23_2023788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_2023788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023788 prefixEnd_2023788 := by exact prefixLift 2023788
  have htrace : WordTrace (prefixWord ++ tailWord_2023788) baseStart_2023788 baseEnd_2023788 := by
    simpa [prefixWord, tailWord_2023788, baseEnd_2023788] using wordTrace_append hprefix tailTrace_2023788
  have hstable : (prefixWord ++ tailWord_2023788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023788).length < 2 ^ (prefixWord ++ tailWord_2023788).sum := by decide
  have hdescent : baseEnd_2023788 < baseStart_2023788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023797 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2023797 : Nat := 118140960795 + 2023797 * 2 ^ 59
def prefixEnd_2023797 : Nat := 4983230072969 + 3 ^ 40 * 2023797 * 2
def baseEnd_2023797 : Nat := 1039180608127323618630233

theorem tailTrace_2023797 : CollatzResearch.WordTrace tailWord_2023797 prefixEnd_2023797 1039180608127323618630233 := by
  unfold tailWord_2023797
  simp only [CollatzResearch.WordTrace]
  refine ⟨73813940649136580855141645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49209293766091053903427763 73813940649136580855141645)
  ·
    refine ⟨27680227743426217820678117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73813940649136580855141645 27680227743426217820678117)
    ·
      refine ⟨5190042701892415841377147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27680227743426217820678117 5190042701892415841377147)
      ·
        refine ⟨7785064052838623762065721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5190042701892415841377147 7785064052838623762065721)
        ·
          refine ⟨5838798039628967821549291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7785064052838623762065721 5838798039628967821549291)
          ·
            refine ⟨8758197059443451732323937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838798039628967821549291 8758197059443451732323937)
            ·
              refine ⟨6568647794582588799242953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8758197059443451732323937 6568647794582588799242953)
              ·
                refine ⟨4926485845936941599432215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6568647794582588799242953 4926485845936941599432215)
                ·
                  refine ⟨7389728768905412399148323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926485845936941599432215 7389728768905412399148323)
                  ·
                    refine ⟨11084593153358118598722485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7389728768905412399148323 11084593153358118598722485)
                    ·
                      refine ⟨1039180608127323618630233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11084593153358118598722485 1039180608127323618630233)
                      ·
                        rfl

theorem cell23_2023797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2023797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023797 prefixEnd_2023797 := by exact prefixLift 2023797
  have htrace : WordTrace (prefixWord ++ tailWord_2023797) baseStart_2023797 baseEnd_2023797 := by
    simpa [prefixWord, tailWord_2023797, baseEnd_2023797] using wordTrace_append hprefix tailTrace_2023797
  have hstable : (prefixWord ++ tailWord_2023797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023797).length < 2 ^ (prefixWord ++ tailWord_2023797).sum := by decide
  have hdescent : baseEnd_2023797 < baseStart_2023797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023811 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 1, 1, 4]
def baseStart_2023811 : Nat := 118140960795 + 2023811 * 2 ^ 59
def prefixEnd_2023811 : Nat := 4983230072969 + 3 ^ 40 * 2023811 * 2
def baseEnd_2023811 : Nat := 1039187796856486563855169

theorem tailTrace_2023811 : CollatzResearch.WordTrace tailWord_2023811 prefixEnd_2023811 1039187796856486563855169 := by
  unfold tailWord_2023811
  simp only [CollatzResearch.WordTrace]
  refine ⟨73814451271085861246151287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49209634180723907497434191 73814451271085861246151287)
  ·
    refine ⟨110721676906628791869226931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73814451271085861246151287 110721676906628791869226931)
    ·
      refine ⟨166082515359943187803840397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110721676906628791869226931 166082515359943187803840397)
      ·
        refine ⟨62280943259978695426440149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166082515359943187803840397 62280943259978695426440149)
        ·
          refine ⟨1459709607655750674057191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62280943259978695426440149 1459709607655750674057191)
          ·
            refine ⟨2189564411483626011085787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459709607655750674057191 2189564411483626011085787)
            ·
              refine ⟨3284346617225439016628681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189564411483626011085787 3284346617225439016628681)
              ·
                refine ⟨2463259962919079262471511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3284346617225439016628681 2463259962919079262471511)
                ·
                  refine ⟨3694889944378618893707267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463259962919079262471511 3694889944378618893707267)
                  ·
                    refine ⟨5542334916567928340560901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3694889944378618893707267 5542334916567928340560901)
                    ·
                      refine ⟨1039187796856486563855169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5542334916567928340560901 1039187796856486563855169)
                      ·
                        rfl

theorem cell23_2023811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_2023811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023811 prefixEnd_2023811 := by exact prefixLift 2023811
  have htrace : WordTrace (prefixWord ++ tailWord_2023811) baseStart_2023811 baseEnd_2023811 := by
    simpa [prefixWord, tailWord_2023811, baseEnd_2023811] using wordTrace_append hprefix tailTrace_2023811
  have hstable : (prefixWord ++ tailWord_2023811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023811).length < 2 ^ (prefixWord ++ tailWord_2023811).sum := by decide
  have hdescent : baseEnd_2023811 < baseStart_2023811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023844 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_2023844 : Nat := 118140960795 + 2023844 * 2 ^ 59
def prefixEnd_2023844 : Nat := 4983230072969 + 3 ^ 40 * 2023844 * 2
def baseEnd_2023844 : Nat := 1039204741718084934742517

theorem tailTrace_2023844 : CollatzResearch.WordTrace tailWord_2023844 prefixEnd_2023844 1039204741718084934742517 := by
  unfold tailWord_2023844
  simp only [CollatzResearch.WordTrace]
  refine ⟨36907827439983153941051293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49210436586644205254735057 36907827439983153941051293)
  ·
    refine ⟨13840435289993682727894235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36907827439983153941051293 13840435289993682727894235)
    ·
      refine ⟨20760652934990524091841353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13840435289993682727894235 20760652934990524091841353)
      ·
        refine ⟨15570489701242893068881015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20760652934990524091841353 15570489701242893068881015)
        ·
          refine ⟨23355734551864339603321523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15570489701242893068881015 23355734551864339603321523)
          ·
            refine ⟨35033601827796509404982285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23355734551864339603321523 35033601827796509404982285)
            ·
              refine ⟨13137600685423691026868357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35033601827796509404982285 13137600685423691026868357)
              ·
                refine ⟨2463300128516942067537817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13137600685423691026868357 2463300128516942067537817)
                ·
                  refine ⟨1847475096387706550653363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463300128516942067537817 1847475096387706550653363)
                  ·
                    refine ⟨2771212644581559825980045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1847475096387706550653363 2771212644581559825980045)
                    ·
                      refine ⟨1039204741718084934742517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2771212644581559825980045 1039204741718084934742517)
                      ·
                        rfl

theorem cell23_2023844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_2023844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023844 prefixEnd_2023844 := by exact prefixLift 2023844
  have htrace : WordTrace (prefixWord ++ tailWord_2023844) baseStart_2023844 baseEnd_2023844 := by
    simpa [prefixWord, tailWord_2023844, baseEnd_2023844] using wordTrace_append hprefix tailTrace_2023844
  have hstable : (prefixWord ++ tailWord_2023844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023844).length < 2 ^ (prefixWord ++ tailWord_2023844).sum := by decide
  have hdescent : baseEnd_2023844 < baseStart_2023844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023901 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_2023901 : Nat := 118140960795 + 2023901 * 2 ^ 59
def prefixEnd_2023901 : Nat := 4983230072969 + 3 ^ 40 * 2023901 * 2
def baseEnd_2023901 : Nat := 1039234010115391211729755

theorem tailTrace_2023901 : CollatzResearch.WordTrace tailWord_2023901 prefixEnd_2023901 1039234010115391211729755 := by
  unfold tailWord_2023901
  simp only [CollatzResearch.WordTrace]
  refine ⟨73817733840759806616927557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49211822560506537744618371 73817733840759806616927557)
  ·
    refine ⟨13840825095142463740673917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73817733840759806616927557 13840825095142463740673917)
    ·
      refine ⟨5190309410678423902752719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13840825095142463740673917 5190309410678423902752719)
      ·
        refine ⟨7785464116017635854129079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5190309410678423902752719 7785464116017635854129079)
        ·
          refine ⟨11678196174026453781193619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7785464116017635854129079 11678196174026453781193619)
          ·
            refine ⟨17517294261039680671790429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11678196174026453781193619 17517294261039680671790429)
            ·
              refine ⟨6568985347889880251921411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17517294261039680671790429 6568985347889880251921411)
              ·
                refine ⟨9853478021834820377882117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568985347889880251921411 9853478021834820377882117)
                ·
                  refine ⟨1847527129094028820852897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9853478021834820377882117 1847527129094028820852897)
                  ·
                    refine ⟨1385645346820521615639673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1847527129094028820852897 1385645346820521615639673)
                    ·
                      refine ⟨1039234010115391211729755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385645346820521615639673 1039234010115391211729755)
                      ·
                        rfl

theorem cell23_2023901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_2023901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023901 prefixEnd_2023901 := by exact prefixLift 2023901
  have htrace : WordTrace (prefixWord ++ tailWord_2023901) baseStart_2023901 baseEnd_2023901 := by
    simpa [prefixWord, tailWord_2023901, baseEnd_2023901] using wordTrace_append hprefix tailTrace_2023901
  have hstable : (prefixWord ++ tailWord_2023901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023901).length < 2 ^ (prefixWord ++ tailWord_2023901).sum := by decide
  have hdescent : baseEnd_2023901 < baseStart_2023901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023920 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 3, 7]
def baseStart_2023920 : Nat := 118140960795 + 2023920 * 2 ^ 59
def prefixEnd_2023920 : Nat := 4983230072969 + 3 ^ 40 * 2023920 * 2
def baseEnd_2023920 : Nat := 346414588749275545797389

theorem tailTrace_2023920 : CollatzResearch.WordTrace tailWord_2023920 prefixEnd_2023920 346414588749275545797389 := by
  unfold tailWord_2023920
  simp only [CollatzResearch.WordTrace]
  refine ⟨36909213413845486430934607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49212284551793981907912809 36909213413845486430934607)
  ·
    refine ⟨55363820120768229646401911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36909213413845486430934607 55363820120768229646401911)
    ·
      refine ⟨83045730181152344469602867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55363820120768229646401911 83045730181152344469602867)
      ·
        refine ⟨124568595271728516704404301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83045730181152344469602867 124568595271728516704404301)
        ·
          refine ⟨46713223226898193764151613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124568595271728516704404301 46713223226898193764151613)
          ·
            refine ⟨17517458710086822661556855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46713223226898193764151613 17517458710086822661556855)
            ·
              refine ⟨26276188065130233992335283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17517458710086822661556855 26276188065130233992335283)
              ·
                refine ⟨39414282097695350988502925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26276188065130233992335283 39414282097695350988502925)
                ·
                  refine ⟨14780355786635756620688597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39414282097695350988502925 14780355786635756620688597)
                  ·
                    refine ⟨346414588749275545797389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14780355786635756620688597 346414588749275545797389)
                    ·
                      rfl

theorem cell23_2023920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_2023920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023920 prefixEnd_2023920 := by exact prefixLift 2023920
  have htrace : WordTrace (prefixWord ++ tailWord_2023920) baseStart_2023920 baseEnd_2023920 := by
    simpa [prefixWord, tailWord_2023920, baseEnd_2023920] using wordTrace_append hprefix tailTrace_2023920
  have hstable : (prefixWord ++ tailWord_2023920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023920).length < 2 ^ (prefixWord ++ tailWord_2023920).sum := by decide
  have hdescent : baseEnd_2023920 < baseStart_2023920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023927 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 7, 2]
def baseStart_2023927 : Nat := 118140960795 + 2023927 * 2 ^ 59
def prefixEnd_2023927 : Nat := 4983230072969 + 3 ^ 40 * 2023927 * 2
def baseEnd_2023927 : Nat := 1039247360612408110004635

theorem tailTrace_2023927 : CollatzResearch.WordTrace tailWord_2023927 prefixEnd_2023927 1039247360612408110004635 := by
  unfold tailWord_2023927
  simp only [CollatzResearch.WordTrace]
  refine ⟨73818682138665613057374035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49212454759110408704916023 73818682138665613057374035)
  ·
    refine ⟨110728023207998419586061053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73818682138665613057374035 110728023207998419586061053)
    ·
      refine ⟨41523008702999407344772895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110728023207998419586061053 41523008702999407344772895)
      ·
        refine ⟨62284513054499111017159343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41523008702999407344772895 62284513054499111017159343)
        ·
          refine ⟨93426769581748666525739015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62284513054499111017159343 93426769581748666525739015)
          ·
            refine ⟨140140154372622999788608523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93426769581748666525739015 140140154372622999788608523)
            ·
              refine ⟨210210231558934499682912785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140140154372622999788608523 210210231558934499682912785)
              ·
                refine ⟨157657673669200874762184589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210210231558934499682912785 157657673669200874762184589)
                ·
                  refine ⟨59121627625950328035819221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157657673669200874762184589 59121627625950328035819221)
                  ·
                    refine ⟨1385663147483210813339513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59121627625950328035819221 1385663147483210813339513)
                    ·
                      refine ⟨1039247360612408110004635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385663147483210813339513 1039247360612408110004635)
                      ·
                        rfl

theorem cell23_2023927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_2023927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023927 prefixEnd_2023927 := by exact prefixLift 2023927
  have htrace : WordTrace (prefixWord ++ tailWord_2023927) baseStart_2023927 baseEnd_2023927 := by
    simpa [prefixWord, tailWord_2023927, baseEnd_2023927] using wordTrace_append hprefix tailTrace_2023927
  have hstable : (prefixWord ++ tailWord_2023927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023927).length < 2 ^ (prefixWord ++ tailWord_2023927).sum := by decide
  have hdescent : baseEnd_2023927 < baseStart_2023927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023930 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_2023930 : Nat := 118140960795 + 2023930 * 2 ^ 59
def prefixEnd_2023930 : Nat := 4983230072969 + 3 ^ 40 * 2023930 * 2
def baseEnd_2023930 : Nat := 1039248901054371598267121

theorem tailTrace_2023930 : CollatzResearch.WordTrace tailWord_2023930 prefixEnd_2023930 1039248901054371598267121 := by
  unfold tailWord_2023930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18454697889413686142433311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49212527705103163046488829 18454697889413686142433311)
  ·
    refine ⟨27682046834120529213649967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18454697889413686142433311 27682046834120529213649967)
    ·
      refine ⟨41523070251180793820474951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27682046834120529213649967 41523070251180793820474951)
      ·
        refine ⟨62284605376771190730712427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41523070251180793820474951 62284605376771190730712427)
        ·
          refine ⟨93426908065156786096068641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62284605376771190730712427 93426908065156786096068641)
          ·
            refine ⟨70070181048867589572051481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93426908065156786096068641 70070181048867589572051481)
            ·
              refine ⟨52552635786650692179038611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70070181048867589572051481 52552635786650692179038611)
              ·
                refine ⟨78828953679976038268557917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52552635786650692179038611 78828953679976038268557917)
                ·
                  refine ⟨29560857629991014350709219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78828953679976038268557917 29560857629991014350709219)
                  ·
                    refine ⟨44341286444986521526063829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29560857629991014350709219 44341286444986521526063829)
                    ·
                      refine ⟨1039248901054371598267121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44341286444986521526063829 1039248901054371598267121)
                      ·
                        rfl

theorem cell23_2023930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_2023930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023930 prefixEnd_2023930 := by exact prefixLift 2023930
  have htrace : WordTrace (prefixWord ++ tailWord_2023930) baseStart_2023930 baseEnd_2023930 := by
    simpa [prefixWord, tailWord_2023930, baseEnd_2023930] using wordTrace_append hprefix tailTrace_2023930
  have hstable : (prefixWord ++ tailWord_2023930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023930).length < 2 ^ (prefixWord ++ tailWord_2023930).sum := by decide
  have hdescent : baseEnd_2023930 < baseStart_2023930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023937 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2023937 : Nat := 118140960795 + 2023937 * 2 ^ 59
def prefixEnd_2023937 : Nat := 4983230072969 + 3 ^ 40 * 2023937 * 2
def baseEnd_2023937 : Nat := 346417498472984356959863

theorem tailTrace_2023937 : CollatzResearch.WordTrace tailWord_2023937 prefixEnd_2023937 346417498472984356959863 := by
  unfold tailWord_2023937
  simp only [CollatzResearch.WordTrace]
  refine ⟨73819046868629384765238065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49212697912419589843492043 73819046868629384765238065)
  ·
    refine ⟨55364285151472038573928549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73819046868629384765238065 55364285151472038573928549)
    ·
      refine ⟨10380803465901007232611603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55364285151472038573928549 10380803465901007232611603)
      ·
        refine ⟨15571205198851510848917405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10380803465901007232611603 15571205198851510848917405)
        ·
          refine ⟨5839201949569316568344027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15571205198851510848917405 5839201949569316568344027)
          ·
            refine ⟨8758802924353974852516041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5839201949569316568344027 8758802924353974852516041)
            ·
              refine ⟨6569102193265481139387031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8758802924353974852516041 6569102193265481139387031)
              ·
                refine ⟨9853653289898221709080547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6569102193265481139387031 9853653289898221709080547)
                ·
                  refine ⟨14780479934847332563620821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9853653289898221709080547 14780479934847332563620821)
                  ·
                    refine ⟨346417498472984356959863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14780479934847332563620821 346417498472984356959863)
                    ·
                      rfl

theorem cell23_2023937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2023937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023937 prefixEnd_2023937 := by exact prefixLift 2023937
  have htrace : WordTrace (prefixWord ++ tailWord_2023937) baseStart_2023937 baseEnd_2023937 := by
    simpa [prefixWord, tailWord_2023937, baseEnd_2023937] using wordTrace_append hprefix tailTrace_2023937
  have hstable : (prefixWord ++ tailWord_2023937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023937).length < 2 ^ (prefixWord ++ tailWord_2023937).sum := by decide
  have hdescent : baseEnd_2023937 < baseStart_2023937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023988 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2023988 : Nat := 118140960795 + 2023988 * 2 ^ 59
def prefixEnd_2023988 : Nat := 4983230072969 + 3 ^ 40 * 2023988 * 2
def baseEnd_2023988 : Nat := 346426227644110790447285

theorem tailTrace_2023988 : CollatzResearch.WordTrace tailWord_2023988 prefixEnd_2023988 346426227644110790447285 := by
  unfold tailWord_2023988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36910453495722310237672309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49213937994296413650229745 36910453495722310237672309)
  ·
    refine ⟨3460355015223966584781779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36910453495722310237672309 3460355015223966584781779)
    ·
      refine ⟨5190532522835949877172669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3460355015223966584781779 5190532522835949877172669)
      ·
        refine ⟨1946449696063481203939751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5190532522835949877172669 1946449696063481203939751)
        ·
          refine ⟨2919674544095221805909627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946449696063481203939751 2919674544095221805909627)
          ·
            refine ⟨4379511816142832708864441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919674544095221805909627 4379511816142832708864441)
            ·
              refine ⟨3284633862107124531648331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4379511816142832708864441 3284633862107124531648331)
              ·
                refine ⟨4926950793160686797472497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284633862107124531648331 4926950793160686797472497)
                ·
                  refine ⟨3695213094870515098104373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4926950793160686797472497 3695213094870515098104373)
                  ·
                    refine ⟨346426227644110790447285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3695213094870515098104373 346426227644110790447285)
                    ·
                      rfl

theorem cell23_2023988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2023988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023988 prefixEnd_2023988 := by exact prefixLift 2023988
  have htrace : WordTrace (prefixWord ++ tailWord_2023988) baseStart_2023988 baseEnd_2023988 := by
    simpa [prefixWord, tailWord_2023988, baseEnd_2023988] using wordTrace_append hprefix tailTrace_2023988
  have hstable : (prefixWord ++ tailWord_2023988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023988).length < 2 ^ (prefixWord ++ tailWord_2023988).sum := by decide
  have hdescent : baseEnd_2023988 < baseStart_2023988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023994 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_2023994 : Nat := 118140960795 + 2023994 * 2 ^ 59
def prefixEnd_2023994 : Nat := 4983230072969 + 3 ^ 40 * 2023994 * 2
def baseEnd_2023994 : Nat := 1039281763816259347866827

theorem tailTrace_2023994 : CollatzResearch.WordTrace tailWord_2023994 prefixEnd_2023994 1039281763816259347866827 := by
  unfold tailWord_2023994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455281457355720875015759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49214083886281922333375357 18455281457355720875015759)
  ·
    refine ⟨27682922186033581312523639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18455281457355720875015759 27682922186033581312523639)
    ·
      refine ⟨41524383279050371968785459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27682922186033581312523639 41524383279050371968785459)
      ·
        refine ⟨62286574918575557953178189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41524383279050371968785459 62286574918575557953178189)
        ·
          refine ⟨23357465594465834232441821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62286574918575557953178189 23357465594465834232441821)
          ·
            refine ⟨8759049597924687837165683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23357465594465834232441821 8759049597924687837165683)
            ·
              refine ⟨13138574396887031755748525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8759049597924687837165683 13138574396887031755748525)
              ·
                refine ⟨4926965398832636908405697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13138574396887031755748525 4926965398832636908405697)
                ·
                  refine ⟨3695224049124477681304273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4926965398832636908405697 3695224049124477681304273)
                  ·
                    refine ⟨2771418036843358260978205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3695224049124477681304273 2771418036843358260978205)
                    ·
                      refine ⟨1039281763816259347866827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2771418036843358260978205 1039281763816259347866827)
                      ·
                        rfl

theorem cell23_2023994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_2023994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2023994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2023994 prefixEnd_2023994 := by exact prefixLift 2023994
  have htrace : WordTrace (prefixWord ++ tailWord_2023994) baseStart_2023994 baseEnd_2023994 := by
    simpa [prefixWord, tailWord_2023994, baseEnd_2023994] using wordTrace_append hprefix tailTrace_2023994
  have hstable : (prefixWord ++ tailWord_2023994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023994).length < 2 ^ (prefixWord ++ tailWord_2023994).sum := by decide
  have hdescent : baseEnd_2023994 < baseStart_2023994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024061 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2024061 : Nat := 118140960795 + 2024061 * 2 ^ 59
def prefixEnd_2024061 : Nat := 4983230072969 + 3 ^ 40 * 2024061 * 2
def baseEnd_2024061 : Nat := 346438722340036861909673

theorem tailTrace_2024061 : CollatzResearch.WordTrace tailWord_2024061 prefixEnd_2024061 346438722340036861909673 := by
  unfold tailWord_2024061
  simp only [CollatzResearch.WordTrace]
  refine ⟨73823569520180153942752037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49215713013453435961834691 73823569520180153942752037)
  ·
    refine ⟨13841919285033778864266007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73823569520180153942752037 13841919285033778864266007)
    ·
      refine ⟨20762878927550668296399011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13841919285033778864266007 20762878927550668296399011)
      ·
        refine ⟨31144318391326002444598517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20762878927550668296399011 31144318391326002444598517)
        ·
          refine ⟨2919779849186812729181111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31144318391326002444598517 2919779849186812729181111)
          ·
            refine ⟨4379669773780219093771667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919779849186812729181111 4379669773780219093771667)
            ·
              refine ⟨6569504660670328640657501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379669773780219093771667 6569504660670328640657501)
              ·
                refine ⟨2463564247751373240246563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6569504660670328640657501 2463564247751373240246563)
                ·
                  refine ⟨3695346371627059860369845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463564247751373240246563 3695346371627059860369845)
                  ·
                    refine ⟨346438722340036861909673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3695346371627059860369845 346438722340036861909673)
                    ·
                      rfl

theorem cell23_2024061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2024061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024061 prefixEnd_2024061 := by exact prefixLift 2024061
  have htrace : WordTrace (prefixWord ++ tailWord_2024061) baseStart_2024061 baseEnd_2024061 := by
    simpa [prefixWord, tailWord_2024061, baseEnd_2024061] using wordTrace_append hprefix tailTrace_2024061
  have hstable : (prefixWord ++ tailWord_2024061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024061).length < 2 ^ (prefixWord ++ tailWord_2024061).sum := by decide
  have hdescent : baseEnd_2024061 < baseStart_2024061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024087 : List Nat := [1, 1, 3, 3, 2, 1, 2, 10]
def baseStart_2024087 : Nat := 118140960795 + 2024087 * 2 ^ 59
def prefixEnd_2024087 : Nat := 4983230072969 + 3 ^ 40 * 2024087 * 2
def baseEnd_2024087 : Nat := 38493685833967684592737

theorem tailTrace_2024087 : CollatzResearch.WordTrace tailWord_2024087 prefixEnd_2024087 38493685833967684592737 := by
  unfold tailWord_2024087
  simp only [CollatzResearch.WordTrace]
  refine ⟨73824517818085960383198515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49216345212057306922132343 73824517818085960383198515)
  ·
    refine ⟨110736776727128940574797773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73824517818085960383198515 110736776727128940574797773)
    ·
      refine ⟨41526291272673352715549165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110736776727128940574797773 41526291272673352715549165)
      ·
        refine ⟨15572359227252507268330937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41526291272673352715549165 15572359227252507268330937)
        ·
          refine ⟨11679269420439380451248203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15572359227252507268330937 11679269420439380451248203)
          ·
            refine ⟨17518904130659070676872305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11679269420439380451248203 17518904130659070676872305)
            ·
              refine ⟨13139178097994303007654229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17518904130659070676872305 13139178097994303007654229)
              ·
                refine ⟨38493685833967684592737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13139178097994303007654229 38493685833967684592737)
                ·
                  rfl

theorem cell23_2024087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 10].length) (baseStart_2024087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024087 prefixEnd_2024087 := by exact prefixLift 2024087
  have htrace : WordTrace (prefixWord ++ tailWord_2024087) baseStart_2024087 baseEnd_2024087 := by
    simpa [prefixWord, tailWord_2024087, baseEnd_2024087] using wordTrace_append hprefix tailTrace_2024087
  have hstable : (prefixWord ++ tailWord_2024087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024087).length < 2 ^ (prefixWord ++ tailWord_2024087).sum := by decide
  have hdescent : baseEnd_2024087 < baseStart_2024087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024114 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2024114 : Nat := 118140960795 + 2024114 * 2 ^ 59
def prefixEnd_2024114 : Nat := 4983230072969 + 3 ^ 40 * 2024114 * 2
def baseEnd_2024114 : Nat := 1039343381494798878366275

theorem tailTrace_2024114 : CollatzResearch.WordTrace tailWord_2024114 prefixEnd_2024114 1039343381494798878366275 := by
  unfold tailWord_2024114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18456375647247035998607849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49217001725992095996287597 18456375647247035998607849)
  ·
    refine ⟨13842281735435276998955887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18456375647247035998607849 13842281735435276998955887)
    ·
      refine ⟨20763422603152915498433831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13842281735435276998955887 20763422603152915498433831)
      ·
        refine ⟨31145133904729373247650747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20763422603152915498433831 31145133904729373247650747)
        ·
          refine ⟨46717700857094059871476121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31145133904729373247650747 46717700857094059871476121)
          ·
            refine ⟨35038275642820544903607091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46717700857094059871476121 35038275642820544903607091)
            ·
              refine ⟨52557413464230817355410637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35038275642820544903607091 52557413464230817355410637)
              ·
                refine ⟨19709030049086556508278989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52557413464230817355410637 19709030049086556508278989)
                ·
                  refine ⟨7390886268407458690604621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19709030049086556508278989 7390886268407458690604621)
                  ·
                    refine ⟨2771582350652797008976733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7390886268407458690604621 2771582350652797008976733)
                    ·
                      refine ⟨1039343381494798878366275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2771582350652797008976733 1039343381494798878366275)
                      ·
                        rfl

theorem cell23_2024114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2024114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024114 prefixEnd_2024114 := by exact prefixLift 2024114
  have htrace : WordTrace (prefixWord ++ tailWord_2024114) baseStart_2024114 baseEnd_2024114 := by
    simpa [prefixWord, tailWord_2024114, baseEnd_2024114] using wordTrace_append hprefix tailTrace_2024114
  have hstable : (prefixWord ++ tailWord_2024114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024114).length < 2 ^ (prefixWord ++ tailWord_2024114).sum := by decide
  have hdescent : baseEnd_2024114 < baseStart_2024114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024115 : List Nat := [1, 1, 1, 2, 3, 4, 3, 3, 1, 2, 2]
def baseStart_2024115 : Nat := 118140960795 + 2024115 * 2 ^ 59
def prefixEnd_2024115 : Nat := 4983230072969 + 3 ^ 40 * 2024115 * 2
def baseEnd_2024115 : Nat := 1039343894975453374453771

theorem tailTrace_2024115 : CollatzResearch.WordTrace tailWord_2024115 prefixEnd_2024115 1039343894975453374453771 := by
  unfold tailWord_2024115
  simp only [CollatzResearch.WordTrace]
  refine ⟨73825539061984521165217799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49217026041323014110145199 73825539061984521165217799)
  ·
    refine ⟨110738308592976781747826699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73825539061984521165217799 110738308592976781747826699)
    ·
      refine ⟨166107462889465172621740049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110738308592976781747826699 166107462889465172621740049)
      ·
        refine ⟨124580597167098879466305037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166107462889465172621740049 124580597167098879466305037)
        ·
          refine ⟨46717723937662079799864389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124580597167098879466305037 46717723937662079799864389)
          ·
            refine ⟨8759573238311639962474573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46717723937662079799864389 8759573238311639962474573)
            ·
              refine ⟨3284839964366864985927965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8759573238311639962474573 3284839964366864985927965)
              ·
                refine ⟨1231814986637574369722987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3284839964366864985927965 1231814986637574369722987)
                ·
                  refine ⟨1847722479956361554584481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231814986637574369722987 1847722479956361554584481)
                  ·
                    refine ⟨1385791859967271165938361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1847722479956361554584481 1385791859967271165938361)
                    ·
                      refine ⟨1039343894975453374453771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385791859967271165938361 1039343894975453374453771)
                      ·
                        rfl

theorem cell23_2024115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 1, 2, 2].length) (baseStart_2024115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024115 prefixEnd_2024115 := by exact prefixLift 2024115
  have htrace : WordTrace (prefixWord ++ tailWord_2024115) baseStart_2024115 baseEnd_2024115 := by
    simpa [prefixWord, tailWord_2024115, baseEnd_2024115] using wordTrace_append hprefix tailTrace_2024115
  have hstable : (prefixWord ++ tailWord_2024115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024115).length < 2 ^ (prefixWord ++ tailWord_2024115).sum := by decide
  have hdescent : baseEnd_2024115 < baseStart_2024115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024175 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 1, 3, 2]
def baseStart_2024175 : Nat := 118140960795 + 2024175 * 2 ^ 59
def prefixEnd_2024175 : Nat := 4983230072969 + 3 ^ 40 * 2024175 * 2
def baseEnd_2024175 : Nat := 1039374703814723139703495

theorem tailTrace_2024175 : CollatzResearch.WordTrace tailWord_2024175 prefixEnd_2024175 1039374703814723139703495 := by
  unfold tailWord_2024175
  simp only [CollatzResearch.WordTrace]
  refine ⟨73827727441767151412401979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49218484961178100941601319 73827727441767151412401979)
  ·
    refine ⟨110741591162650727118602969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73827727441767151412401979 110741591162650727118602969)
    ·
      refine ⟨83056193371988045338952227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110741591162650727118602969 83056193371988045338952227)
      ·
        refine ⟨124584290057982068008428341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83056193371988045338952227 124584290057982068008428341)
        ·
          refine ⟨11679777192935818875790157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124584290057982068008428341 11679777192935818875790157)
          ·
            refine ⟨4379916447350932078421309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11679777192935818875790157 4379916447350932078421309)
            ·
              refine ⟨1642468667756599529407991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4379916447350932078421309 1642468667756599529407991)
              ·
                refine ⟨2463703001634899294111987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642468667756599529407991 2463703001634899294111987)
                ·
                  refine ⟨3695554502452348941167981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463703001634899294111987 3695554502452348941167981)
                  ·
                    refine ⟨1385832938419630852937993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3695554502452348941167981 1385832938419630852937993)
                    ·
                      refine ⟨1039374703814723139703495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385832938419630852937993 1039374703814723139703495)
                      ·
                        rfl

theorem cell23_2024175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 3, 2].length) (baseStart_2024175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024175 prefixEnd_2024175 := by exact prefixLift 2024175
  have htrace : WordTrace (prefixWord ++ tailWord_2024175) baseStart_2024175 baseEnd_2024175 := by
    simpa [prefixWord, tailWord_2024175, baseEnd_2024175] using wordTrace_append hprefix tailTrace_2024175
  have hstable : (prefixWord ++ tailWord_2024175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024175).length < 2 ^ (prefixWord ++ tailWord_2024175).sum := by decide
  have hdescent : baseEnd_2024175 < baseStart_2024175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024184 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_2024184 : Nat := 118140960795 + 2024184 * 2 ^ 59
def prefixEnd_2024184 : Nat := 4983230072969 + 3 ^ 40 * 2024184 * 2
def baseEnd_2024184 : Nat := 1039379325140613604490953

theorem tailTrace_2024184 : CollatzResearch.WordTrace tailWord_2024184 prefixEnd_2024184 1039379325140613604490953 := by
  unfold tailWord_2024184
  simp only [CollatzResearch.WordTrace]
  refine ⟨36914027849367272974739803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49218703799156363966319737 36914027849367272974739803)
  ·
    refine ⟨55371041774050909462109705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36914027849367272974739803 55371041774050909462109705)
    ·
      refine ⟨41528281330538182096582279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55371041774050909462109705 41528281330538182096582279)
      ·
        refine ⟨62292421995807273144873419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41528281330538182096582279 62292421995807273144873419)
        ·
          refine ⟨93438632993710909717310129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62292421995807273144873419 93438632993710909717310129)
          ·
            refine ⟨70078974745283182287982597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93438632993710909717310129 70078974745283182287982597)
            ·
              refine ⟨13139807764740596678996737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70078974745283182287982597 13139807764740596678996737)
              ·
                refine ⟨9854855823555447509247553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13139807764740596678996737 9854855823555447509247553)
                ·
                  refine ⟨7391141867666585631935665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9854855823555447509247553 7391141867666585631935665)
                  ·
                    refine ⟨5543356400749939223951749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7391141867666585631935665 5543356400749939223951749)
                    ·
                      refine ⟨1039379325140613604490953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5543356400749939223951749 1039379325140613604490953)
                      ·
                        rfl

theorem cell23_2024184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_2024184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024184 prefixEnd_2024184 := by exact prefixLift 2024184
  have htrace : WordTrace (prefixWord ++ tailWord_2024184) baseStart_2024184 baseEnd_2024184 := by
    simpa [prefixWord, tailWord_2024184, baseEnd_2024184] using wordTrace_append hprefix tailTrace_2024184
  have hstable : (prefixWord ++ tailWord_2024184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024184).length < 2 ^ (prefixWord ++ tailWord_2024184).sum := by decide
  have hdescent : baseEnd_2024184 < baseStart_2024184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024238 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2024238 : Nat := 118140960795 + 2024238 * 2 ^ 59
def prefixEnd_2024238 : Nat := 4983230072969 + 3 ^ 40 * 2024238 * 2
def baseEnd_2024238 : Nat := 1039407053095956393215705

theorem tailTrace_2024238 : CollatzResearch.WordTrace tailWord_2024238 prefixEnd_2024238 1039407053095956393215705 := by
  unfold tailWord_2024238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9228753155067364146493171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49220016827025942114630245 9228753155067364146493171)
  ·
    refine ⟨13843129732601046219739757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9228753155067364146493171 13843129732601046219739757)
    ·
      refine ⟨5191173649725392332402409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13843129732601046219739757 5191173649725392332402409)
      ·
        refine ⟨3893380237294044249301807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5191173649725392332402409 3893380237294044249301807)
        ·
          refine ⟨5840070355941066373952711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893380237294044249301807 5840070355941066373952711)
          ·
            refine ⟨8760105533911599560929067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840070355941066373952711 8760105533911599560929067)
            ·
              refine ⟨13140158300867399341393601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8760105533911599560929067 13140158300867399341393601)
              ·
                refine ⟨9855118725650549506045201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13140158300867399341393601 9855118725650549506045201)
                ·
                  refine ⟨7391339044237912129533901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9855118725650549506045201 7391339044237912129533901)
                  ·
                    refine ⟨2771752141589217048575213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7391339044237912129533901 2771752141589217048575213)
                    ·
                      refine ⟨1039407053095956393215705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2771752141589217048575213 1039407053095956393215705)
                      ·
                        rfl

theorem cell23_2024238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2024238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024238 prefixEnd_2024238 := by exact prefixLift 2024238
  have htrace : WordTrace (prefixWord ++ tailWord_2024238) baseStart_2024238 baseEnd_2024238 := by
    simpa [prefixWord, tailWord_2024238, baseEnd_2024238] using wordTrace_append hprefix tailTrace_2024238
  have hstable : (prefixWord ++ tailWord_2024238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024238).length < 2 ^ (prefixWord ++ tailWord_2024238).sum := by decide
  have hdescent : baseEnd_2024238 < baseStart_2024238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024261 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 1, 6, 2]
def baseStart_2024261 : Nat := 118140960795 + 2024261 * 2 ^ 59
def prefixEnd_2024261 : Nat := 4983230072969 + 3 ^ 40 * 2024261 * 2
def baseEnd_2024261 : Nat := 1039418863151009803228099

theorem tailTrace_2024261 : CollatzResearch.WordTrace tailWord_2024261 prefixEnd_2024261 1039418863151009803228099 := by
  unfold tailWord_2024261
  simp only [CollatzResearch.WordTrace]
  refine ⟨73830864119455588100032637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49220576079637058733355091 73830864119455588100032637)
  ·
    refine ⟨27686574044795845537512239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73830864119455588100032637 27686574044795845537512239)
    ·
      refine ⟨41529861067193768306268359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27686574044795845537512239 41529861067193768306268359)
      ·
        refine ⟨62294791600790652459402539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41529861067193768306268359 62294791600790652459402539)
        ·
          refine ⟨93442187401185978689103809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62294791600790652459402539 93442187401185978689103809)
          ·
            refine ⟨70081640550889484016827857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93442187401185978689103809 70081640550889484016827857)
            ·
              refine ⟨52561230413167113012620893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70081640550889484016827857 52561230413167113012620893)
              ·
                refine ⟨19710461404937667379732835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52561230413167113012620893 19710461404937667379732835)
                ·
                  refine ⟨29565692107406501069599253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19710461404937667379732835 29565692107406501069599253)
                  ·
                    refine ⟨1385891817534679737637465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29565692107406501069599253 1385891817534679737637465)
                    ·
                      refine ⟨1039418863151009803228099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1385891817534679737637465 1039418863151009803228099)
                      ·
                        rfl

theorem cell23_2024261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_2024261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024261 prefixEnd_2024261 := by exact prefixLift 2024261
  have htrace : WordTrace (prefixWord ++ tailWord_2024261) baseStart_2024261 baseEnd_2024261 := by
    simpa [prefixWord, tailWord_2024261, baseEnd_2024261] using wordTrace_append hprefix tailTrace_2024261
  have hstable : (prefixWord ++ tailWord_2024261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024261).length < 2 ^ (prefixWord ++ tailWord_2024261).sum := by decide
  have hdescent : baseEnd_2024261 < baseStart_2024261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024281 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 3]
def baseStart_2024281 : Nat := 118140960795 + 2024281 * 2 ^ 59
def prefixEnd_2024281 : Nat := 4983230072969 + 3 ^ 40 * 2024281 * 2
def baseEnd_2024281 : Nat := 1039429132764099724978007

theorem tailTrace_2024281 : CollatzResearch.WordTrace tailWord_2024281 prefixEnd_2024281 1039429132764099724978007 := by
  unfold tailWord_2024281
  simp only [CollatzResearch.WordTrace]
  refine ⟨73831593579383131515760697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49221062386255421010507131 73831593579383131515760697)
  ·
    refine ⟨55373695184537348636820523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73831593579383131515760697 55373695184537348636820523)
    ·
      refine ⟨83060542776806022955230785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55373695184537348636820523 83060542776806022955230785)
      ·
        refine ⟨62295407082604517216423089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83060542776806022955230785 62295407082604517216423089)
        ·
          refine ⟨46721555311953387912317317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62295407082604517216423089 46721555311953387912317317)
          ·
            refine ⟨8760291620991260233559497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46721555311953387912317317 8760291620991260233559497)
            ·
              refine ⟨6570218715743445175169623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8760291620991260233559497 6570218715743445175169623)
              ·
                refine ⟨9855328073615167762754435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6570218715743445175169623 9855328073615167762754435)
                ·
                  refine ⟨14782992110422751644131653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9855328073615167762754435 14782992110422751644131653)
                  ·
                    refine ⟨2771811020704265933274685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14782992110422751644131653 2771811020704265933274685)
                    ·
                      refine ⟨1039429132764099724978007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2771811020704265933274685 1039429132764099724978007)
                      ·
                        rfl

theorem cell23_2024281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_2024281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024281 prefixEnd_2024281 := by exact prefixLift 2024281
  have htrace : WordTrace (prefixWord ++ tailWord_2024281) baseStart_2024281 baseEnd_2024281 := by
    simpa [prefixWord, tailWord_2024281, baseEnd_2024281] using wordTrace_append hprefix tailTrace_2024281
  have hstable : (prefixWord ++ tailWord_2024281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024281).length < 2 ^ (prefixWord ++ tailWord_2024281).sum := by decide
  have hdescent : baseEnd_2024281 < baseStart_2024281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024301 : List Nat := [1, 5, 1, 1, 1, 1, 1, 6, 6]
def baseStart_2024301 : Nat := 118140960795 + 2024301 * 2 ^ 59
def prefixEnd_2024301 : Nat := 4983230072969 + 3 ^ 40 * 2024301 * 2
def baseEnd_2024301 : Nat := 115493266930798849636435

theorem tailTrace_2024301 : CollatzResearch.WordTrace tailWord_2024301 prefixEnd_2024301 115493266930798849636435 := by
  unfold tailWord_2024301
  simp only [CollatzResearch.WordTrace]
  refine ⟨73832323039310674931488757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49221548692873783287659171 73832323039310674931488757)
  ·
    refine ⟨6921780284935375774827071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73832323039310674931488757 6921780284935375774827071)
    ·
      refine ⟨10382670427403063662240607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6921780284935375774827071 10382670427403063662240607)
      ·
        refine ⟨15574005641104595493360911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10382670427403063662240607 15574005641104595493360911)
        ·
          refine ⟨23361008461656893240041367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15574005641104595493360911 23361008461656893240041367)
          ·
            refine ⟨35041512692485339860062051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23361008461656893240041367 35041512692485339860062051)
            ·
              refine ⟨52562269038728009790093077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35041512692485339860062051 52562269038728009790093077)
              ·
                refine ⟨2463856361190375458910613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52562269038728009790093077 2463856361190375458910613)
                ·
                  refine ⟨115493266930798849636435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2463856361190375458910613 115493266930798849636435)
                  ·
                    rfl

theorem cell23_2024301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_2024301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024301 prefixEnd_2024301 := by exact prefixLift 2024301
  have htrace : WordTrace (prefixWord ++ tailWord_2024301) baseStart_2024301 baseEnd_2024301 := by
    simpa [prefixWord, tailWord_2024301, baseEnd_2024301] using wordTrace_append hprefix tailTrace_2024301
  have hstable : (prefixWord ++ tailWord_2024301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024301).length < 2 ^ (prefixWord ++ tailWord_2024301).sum := by decide
  have hdescent : baseEnd_2024301 < baseStart_2024301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024304 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_2024304 : Nat := 118140960795 + 2024304 * 2 ^ 59
def prefixEnd_2024304 : Nat := 4983230072969 + 3 ^ 40 * 2024304 * 2
def baseEnd_2024304 : Nat := 1039440942819153134990401

theorem tailTrace_2024304 : CollatzResearch.WordTrace tailWord_2024304 prefixEnd_2024304 1039440942819153134990401 := by
  unfold tailWord_2024304
  simp only [CollatzResearch.WordTrace]
  refine ⟨36916216229149903221923983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49221621638866537629231977 36916216229149903221923983)
  ·
    refine ⟨55374324343724854832885975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36916216229149903221923983 55374324343724854832885975)
    ·
      refine ⟨83061486515587282249328963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55374324343724854832885975 83061486515587282249328963)
      ·
        refine ⟨124592229773380923373993445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83061486515587282249328963 124592229773380923373993445)
        ·
          refine ⟨23361043082508923132623771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124592229773380923373993445 23361043082508923132623771)
          ·
            refine ⟨35041564623763384698935657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23361043082508923132623771 35041564623763384698935657)
            ·
              refine ⟨26281173467822538524201743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35041564623763384698935657 26281173467822538524201743)
              ·
                refine ⟨39421760201733807786302615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26281173467822538524201743 39421760201733807786302615)
                ·
                  refine ⟨59132640302600711679453923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39421760201733807786302615 59132640302600711679453923)
                  ·
                    refine ⟨88698960453901067519180885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59132640302600711679453923 88698960453901067519180885)
                    ·
                      refine ⟨1039440942819153134990401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88698960453901067519180885 1039440942819153134990401)
                      ·
                        rfl

theorem cell23_2024304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_2024304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024304 prefixEnd_2024304 := by exact prefixLift 2024304
  have htrace : WordTrace (prefixWord ++ tailWord_2024304) baseStart_2024304 baseEnd_2024304 := by
    simpa [prefixWord, tailWord_2024304, baseEnd_2024304] using wordTrace_append hprefix tailTrace_2024304
  have hstable : (prefixWord ++ tailWord_2024304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024304).length < 2 ^ (prefixWord ++ tailWord_2024304).sum := by decide
  have hdescent : baseEnd_2024304 < baseStart_2024304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024314 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_2024314 : Nat := 118140960795 + 2024314 * 2 ^ 59
def prefixEnd_2024314 : Nat := 4983230072969 + 3 ^ 40 * 2024314 * 2
def baseEnd_2024314 : Nat := 346482025875232698621785

theorem tailTrace_2024314 : CollatzResearch.WordTrace tailWord_2024314 prefixEnd_2024314 346482025875232698621785 := by
  unfold tailWord_2024314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458199297065894537927999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49221864792175718767807997 18458199297065894537927999)
  ·
    refine ⟨27687298945598841806891999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458199297065894537927999 27687298945598841806891999)
    ·
      refine ⟨41530948418398262710337999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27687298945598841806891999 41530948418398262710337999)
      ·
        refine ⟨62296422627597394065506999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41530948418398262710337999 62296422627597394065506999)
        ·
          refine ⟨93444633941396091098260499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62296422627597394065506999 93444633941396091098260499)
          ·
            refine ⟨140166950912094136647390749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93444633941396091098260499 140166950912094136647390749)
            ·
              refine ⟨52562606592035301242771531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140166950912094136647390749 52562606592035301242771531)
              ·
                refine ⟨78843909888052951864157297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52562606592035301242771531 78843909888052951864157297)
                ·
                  refine ⟨59132932416039713898117973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78843909888052951864157297 59132932416039713898117973)
                  ·
                    refine ⟨346482025875232698621785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 59132932416039713898117973 346482025875232698621785)
                    ·
                      rfl

theorem cell23_2024314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_2024314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024314 prefixEnd_2024314 := by exact prefixLift 2024314
  have htrace : WordTrace (prefixWord ++ tailWord_2024314) baseStart_2024314 baseEnd_2024314 := by
    simpa [prefixWord, tailWord_2024314, baseEnd_2024314] using wordTrace_append hprefix tailTrace_2024314
  have hstable : (prefixWord ++ tailWord_2024314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024314).length < 2 ^ (prefixWord ++ tailWord_2024314).sum := by decide
  have hdescent : baseEnd_2024314 < baseStart_2024314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024345 : List Nat := [1, 2, 1, 2, 1, 3, 1, 7, 1, 1, 3]
def baseStart_2024345 : Nat := 118140960795 + 2024345 * 2 ^ 59
def prefixEnd_2024345 : Nat := 4983230072969 + 3 ^ 40 * 2024345 * 2
def baseEnd_2024345 : Nat := 1039461995525987474577713

theorem tailTrace_2024345 : CollatzResearch.WordTrace tailWord_2024345 prefixEnd_2024345 1039461995525987474577713 := by
  unfold tailWord_2024345
  simp only [CollatzResearch.WordTrace]
  refine ⟨73833927851151270446090489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49222618567434180297393659 73833927851151270446090489)
  ·
    refine ⟨55375445888363452834567867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73833927851151270446090489 55375445888363452834567867)
    ·
      refine ⟨83063168832545179251851801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55375445888363452834567867 83063168832545179251851801)
      ·
        refine ⟨62297376624408884438888851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83063168832545179251851801 62297376624408884438888851)
        ·
          refine ⟨93446064936613326658333277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62297376624408884438888851 93446064936613326658333277)
          ·
            refine ⟨35042274351229997496874979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93446064936613326658333277 35042274351229997496874979)
            ·
              refine ⟨52563411526844996245312469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35042274351229997496874979 52563411526844996245312469)
              ·
                refine ⟨1231954957660429599499511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52563411526844996245312469 1231954957660429599499511)
                ·
                  refine ⟨1847932436490644399249267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231954957660429599499511 1847932436490644399249267)
                  ·
                    refine ⟨2771898654735966598873901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1847932436490644399249267 2771898654735966598873901)
                    ·
                      refine ⟨1039461995525987474577713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2771898654735966598873901 1039461995525987474577713)
                      ·
                        rfl

theorem cell23_2024345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_2024345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024345 prefixEnd_2024345 := by exact prefixLift 2024345
  have htrace : WordTrace (prefixWord ++ tailWord_2024345) baseStart_2024345 baseEnd_2024345 := by
    simpa [prefixWord, tailWord_2024345, baseEnd_2024345] using wordTrace_append hprefix tailTrace_2024345
  have hstable : (prefixWord ++ tailWord_2024345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024345).length < 2 ^ (prefixWord ++ tailWord_2024345).sum := by decide
  have hdescent : baseEnd_2024345 < baseStart_2024345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024378 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 2, 4]
def baseStart_2024378 : Nat := 118140960795 + 2024378 * 2 ^ 59
def prefixEnd_2024378 : Nat := 4983230072969 + 3 ^ 40 * 2024378 * 2
def baseEnd_2024378 : Nat := 346492980129195281821687

theorem tailTrace_2024378 : CollatzResearch.WordTrace tailWord_2024378 prefixEnd_2024378 346492980129195281821687 := by
  unfold tailWord_2024378
  simp only [CollatzResearch.WordTrace]
  refine ⟨18458782865007929270510447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49223420973354478054694525 18458782865007929270510447)
  ·
    refine ⟨27688174297511893905765671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18458782865007929270510447 27688174297511893905765671)
    ·
      refine ⟨41532261446267840858648507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27688174297511893905765671 41532261446267840858648507)
      ·
        refine ⟨62298392169401761287972761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41532261446267840858648507 62298392169401761287972761)
        ·
          refine ⟨46723794127051320965979571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62298392169401761287972761 46723794127051320965979571)
          ·
            refine ⟨70085691190576981448969357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46723794127051320965979571 70085691190576981448969357)
            ·
              refine ⟨26282134196466368043363509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70085691190576981448969357 26282134196466368043363509)
              ·
                refine ⟨2463950080918722004065329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26282134196466368043363509 2463950080918722004065329)
                ·
                  refine ⟨1847962560689041503048997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2463950080918722004065329 1847962560689041503048997)
                  ·
                    refine ⟨346492980129195281821687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1847962560689041503048997 346492980129195281821687)
                    ·
                      rfl

theorem cell23_2024378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_2024378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024378 prefixEnd_2024378 := by exact prefixLift 2024378
  have htrace : WordTrace (prefixWord ++ tailWord_2024378) baseStart_2024378 baseEnd_2024378 := by
    simpa [prefixWord, tailWord_2024378, baseEnd_2024378] using wordTrace_append hprefix tailTrace_2024378
  have hstable : (prefixWord ++ tailWord_2024378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024378).length < 2 ^ (prefixWord ++ tailWord_2024378).sum := by decide
  have hdescent : baseEnd_2024378 < baseStart_2024378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024398 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_2024398 : Nat := 118140960795 + 2024398 * 2 ^ 59
def prefixEnd_2024398 : Nat := 4983230072969 + 3 ^ 40 * 2024398 * 2
def baseEnd_2024398 : Nat := 1039489210000675767214969

theorem tailTrace_2024398 : CollatzResearch.WordTrace tailWord_2024398 prefixEnd_2024398 1039489210000675767214969 := by
  unfold tailWord_2024398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229482614994907562221231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49223907279972840331846565 9229482614994907562221231)
  ·
    refine ⟨13844223922492361343331847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9229482614994907562221231 13844223922492361343331847)
    ·
      refine ⟨20766335883738542014997771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13844223922492361343331847 20766335883738542014997771)
      ·
        refine ⟨31149503825607813022496657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20766335883738542014997771 31149503825607813022496657)
        ·
          refine ⟨23362127869205859766872493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31149503825607813022496657 23362127869205859766872493)
          ·
            refine ⟨8760797950952197412577185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23362127869205859766872493 8760797950952197412577185)
            ·
              refine ⟨6570598463214148059432889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8760797950952197412577185 6570598463214148059432889)
              ·
                refine ⟨4927948847410611044574667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6570598463214148059432889 4927948847410611044574667)
                ·
                  refine ⟨7391923271115916566862001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4927948847410611044574667 7391923271115916566862001)
                  ·
                    refine ⟨5543942453336937425146501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7391923271115916566862001 5543942453336937425146501)
                    ·
                      refine ⟨1039489210000675767214969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5543942453336937425146501 1039489210000675767214969)
                      ·
                        rfl

theorem cell23_2024398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_2024398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024398 prefixEnd_2024398 := by exact prefixLift 2024398
  have htrace : WordTrace (prefixWord ++ tailWord_2024398) baseStart_2024398 baseEnd_2024398 := by
    simpa [prefixWord, tailWord_2024398, baseEnd_2024398] using wordTrace_append hprefix tailTrace_2024398
  have hstable : (prefixWord ++ tailWord_2024398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024398).length < 2 ^ (prefixWord ++ tailWord_2024398).sum := by decide
  have hdescent : baseEnd_2024398 < baseStart_2024398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024402 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2024402 : Nat := 118140960795 + 2024402 * 2 ^ 59
def prefixEnd_2024402 : Nat := 4983230072969 + 3 ^ 40 * 2024402 * 2
def baseEnd_2024402 : Nat := 1039491263923293751564951

theorem tailTrace_2024402 : CollatzResearch.WordTrace tailWord_2024402 prefixEnd_2024402 1039491263923293751564951 := by
  unfold tailWord_2024402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18459001702986192295228865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49224004541296512787276973 18459001702986192295228865)
  ·
    refine ⟨13844251277239644221421649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18459001702986192295228865 13844251277239644221421649)
    ·
      refine ⟨10383188457929733166066237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13844251277239644221421649 10383188457929733166066237)
      ·
        refine ⟨3893695671723649937274839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10383188457929733166066237 3893695671723649937274839)
        ·
          refine ⟨5840543507585474905912259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893695671723649937274839 5840543507585474905912259)
          ·
            refine ⟨8760815261378212358868389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5840543507585474905912259 8760815261378212358868389)
            ·
              refine ⟨1642652861508414817287823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8760815261378212358868389 1642652861508414817287823)
              ·
                refine ⟨2463979292262622225931735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642652861508414817287823 2463979292262622225931735)
                ·
                  refine ⟨3695968938393933338897603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463979292262622225931735 3695968938393933338897603)
                  ·
                    refine ⟨5543953407590900008346405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3695968938393933338897603 5543953407590900008346405)
                    ·
                      refine ⟨1039491263923293751564951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5543953407590900008346405 1039491263923293751564951)
                      ·
                        rfl

theorem cell23_2024402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2024402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024402 prefixEnd_2024402 := by exact prefixLift 2024402
  have htrace : WordTrace (prefixWord ++ tailWord_2024402) baseStart_2024402 baseEnd_2024402 := by
    simpa [prefixWord, tailWord_2024402, baseEnd_2024402] using wordTrace_append hprefix tailTrace_2024402
  have hstable : (prefixWord ++ tailWord_2024402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024402).length < 2 ^ (prefixWord ++ tailWord_2024402).sum := by decide
  have hdescent : baseEnd_2024402 < baseStart_2024402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024462 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_2024462 : Nat := 118140960795 + 2024462 * 2 ^ 59
def prefixEnd_2024462 : Nat := 4983230072969 + 3 ^ 40 * 2024462 * 2
def baseEnd_2024462 : Nat := 1039522072762563516814675

theorem tailTrace_2024462 : CollatzResearch.WordTrace tailWord_2024462 prefixEnd_2024462 1039522072762563516814675 := by
  unfold tailWord_2024462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9229774398965924928512455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49225463461151599618733093 9229774398965924928512455)
  ·
    refine ⟨13844661598448887392768683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9229774398965924928512455 13844661598448887392768683)
    ·
      refine ⟨20766992397673331089153025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13844661598448887392768683 20766992397673331089153025)
      ·
        refine ⟨15575244298254998316864769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20766992397673331089153025 15575244298254998316864769)
        ·
          refine ⟨11681433223691248737648577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15575244298254998316864769 11681433223691248737648577)
          ·
            refine ⟨8761074917768436553236433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11681433223691248737648577 8761074917768436553236433)
            ·
              refine ⟨6570806188326327414927325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8761074917768436553236433 6570806188326327414927325)
              ·
                refine ⟨2464052320622372780597747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6570806188326327414927325 2464052320622372780597747)
                ·
                  refine ⟨3696078480933559170896621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464052320622372780597747 3696078480933559170896621)
                  ·
                    refine ⟨1386029430350084689086233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3696078480933559170896621 1386029430350084689086233)
                    ·
                      refine ⟨1039522072762563516814675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386029430350084689086233 1039522072762563516814675)
                      ·
                        rfl

theorem cell23_2024462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_2024462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024462 prefixEnd_2024462 := by exact prefixLift 2024462
  have htrace : WordTrace (prefixWord ++ tailWord_2024462) baseStart_2024462 baseEnd_2024462 := by
    simpa [prefixWord, tailWord_2024462, baseEnd_2024462] using wordTrace_append hprefix tailTrace_2024462
  have hstable : (prefixWord ++ tailWord_2024462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024462).length < 2 ^ (prefixWord ++ tailWord_2024462).sum := by decide
  have hdescent : baseEnd_2024462 < baseStart_2024462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024492 : List Nat := [2, 2, 1, 1, 1, 2, 5, 3, 2, 2, 2]
def baseStart_2024492 : Nat := 118140960795 + 2024492 * 2 ^ 59
def prefixEnd_2024492 : Nat := 4983230072969 + 3 ^ 40 * 2024492 * 2
def baseEnd_2024492 : Nat := 1039537477182198399439537

theorem tailTrace_2024492 : CollatzResearch.WordTrace tailWord_2024492 prefixEnd_2024492 1039537477182198399439537 := by
  unfold tailWord_2024492
  simp only [CollatzResearch.WordTrace]
  refine ⟨36919644690809357275845865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49226192921079143034461153 36919644690809357275845865)
  ·
    refine ⟨27689733518107017956884399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36919644690809357275845865 27689733518107017956884399)
    ·
      refine ⟨41534600277160526935326599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27689733518107017956884399 41534600277160526935326599)
      ·
        refine ⟨62301900415740790402989899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41534600277160526935326599 62301900415740790402989899)
        ·
          refine ⟨93452850623611185604484849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62301900415740790402989899 93452850623611185604484849)
          ·
            refine ⟨70089637967708389203363637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93452850623611185604484849 70089637967708389203363637)
            ·
              refine ⟨6570903559472661487815341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70089637967708389203363637 6570903559472661487815341)
              ·
                refine ⟨2464088834802248057930753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6570903559472661487815341 2464088834802248057930753)
                ·
                  refine ⟨1848066626101686043448065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2464088834802248057930753 1848066626101686043448065)
                  ·
                    refine ⟨1386049969576264532586049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1848066626101686043448065 1386049969576264532586049)
                    ·
                      refine ⟨1039537477182198399439537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386049969576264532586049 1039537477182198399439537)
                      ·
                        rfl

theorem cell23_2024492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_2024492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024492 prefixEnd_2024492 := by exact prefixLift 2024492
  have htrace : WordTrace (prefixWord ++ tailWord_2024492) baseStart_2024492 baseEnd_2024492 := by
    simpa [prefixWord, tailWord_2024492, baseEnd_2024492] using wordTrace_append hprefix tailTrace_2024492
  have hstable : (prefixWord ++ tailWord_2024492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024492).length < 2 ^ (prefixWord ++ tailWord_2024492).sum := by decide
  have hdescent : baseEnd_2024492 < baseStart_2024492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024532 : List Nat := [2, 4, 1, 1, 1, 1, 6, 2, 5]
def baseStart_2024532 : Nat := 118140960795 + 2024532 * 2 ^ 59
def prefixEnd_2024532 : Nat := 4983230072969 + 3 ^ 40 * 2024532 * 2
def baseEnd_2024532 : Nat := 115506446267597582548817

theorem tailTrace_2024532 : CollatzResearch.WordTrace tailWord_2024532 prefixEnd_2024532 115506446267597582548817 := by
  unfold tailWord_2024532
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920374150736900691573925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49227165534315867588765233 36920374150736900691573925)
  ·
    refine ⟨6922570153263168879670111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36920374150736900691573925 6922570153263168879670111)
    ·
      refine ⟨10383855229894753319505167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6922570153263168879670111 10383855229894753319505167)
      ·
        refine ⟨15575782844842129979257751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10383855229894753319505167 15575782844842129979257751)
        ·
          refine ⟨23363674267263194968886627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15575782844842129979257751 23363674267263194968886627)
          ·
            refine ⟨35045511400894792453329941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23363674267263194968886627 35045511400894792453329941)
            ·
              refine ⟨1642758346916943396249841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35045511400894792453329941 1642758346916943396249841)
              ·
                refine ⟨1232068760187707547187381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642758346916943396249841 1232068760187707547187381)
                ·
                  refine ⟨115506446267597582548817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1232068760187707547187381 115506446267597582548817)
                  ·
                    rfl

theorem cell23_2024532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_2024532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024532 prefixEnd_2024532 := by exact prefixLift 2024532
  have htrace : WordTrace (prefixWord ++ tailWord_2024532) baseStart_2024532 baseEnd_2024532 := by
    simpa [prefixWord, tailWord_2024532, baseEnd_2024532] using wordTrace_append hprefix tailTrace_2024532
  have hstable : (prefixWord ++ tailWord_2024532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024532).length < 2 ^ (prefixWord ++ tailWord_2024532).sum := by decide
  have hdescent : baseEnd_2024532 < baseStart_2024532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024548 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_2024548 : Nat := 118140960795 + 2024548 * 2 ^ 59
def prefixEnd_2024548 : Nat := 4983230072969 + 3 ^ 40 * 2024548 * 2
def baseEnd_2024548 : Nat := 1039566232098850180339279

theorem tailTrace_2024548 : CollatzResearch.WordTrace tailWord_2024548 prefixEnd_2024548 1039566232098850180339279 := by
  unfold tailWord_2024548
  simp only [CollatzResearch.WordTrace]
  refine ⟨36920665934707918057865149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49227554579610557410486865 36920665934707918057865149)
  ·
    refine ⟨13845249725515469271699431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36920665934707918057865149 13845249725515469271699431)
    ·
      refine ⟨20767874588273203907549147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13845249725515469271699431 20767874588273203907549147)
      ·
        refine ⟨31151811882409805861323721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20767874588273203907549147 31151811882409805861323721)
        ·
          refine ⟨23363858911807354395992791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31151811882409805861323721 23363858911807354395992791)
          ·
            refine ⟨35045788367711031593989187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23363858911807354395992791 35045788367711031593989187)
            ·
              refine ⟨52568682551566547390983781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35045788367711031593989187 52568682551566547390983781)
              ·
                refine ⟨9856627978418727635809459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52568682551566547390983781 9856627978418727635809459)
                ·
                  refine ⟨14784941967628091453714189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9856627978418727635809459 14784941967628091453714189)
                  ·
                    refine ⟨5544353237860534295142821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14784941967628091453714189 5544353237860534295142821)
                    ·
                      refine ⟨1039566232098850180339279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5544353237860534295142821 1039566232098850180339279)
                      ·
                        rfl

theorem cell23_2024548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_2024548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024548 prefixEnd_2024548 := by exact prefixLift 2024548
  have htrace : WordTrace (prefixWord ++ tailWord_2024548) baseStart_2024548 baseEnd_2024548 := by
    simpa [prefixWord, tailWord_2024548, baseEnd_2024548] using wordTrace_append hprefix tailTrace_2024548
  have hstable : (prefixWord ++ tailWord_2024548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024548).length < 2 ^ (prefixWord ++ tailWord_2024548).sum := by decide
  have hdescent : baseEnd_2024548 < baseStart_2024548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024608 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2024608 : Nat := 118140960795 + 2024608 * 2 ^ 59
def prefixEnd_2024608 : Nat := 4983230072969 + 3 ^ 40 * 2024608 * 2
def baseEnd_2024608 : Nat := 1039597040938119945589003

theorem tailTrace_2024608 : CollatzResearch.WordTrace tailWord_2024608 prefixEnd_2024608 1039597040938119945589003 := by
  unfold tailWord_2024608
  simp only [CollatzResearch.WordTrace]
  refine ⟨36921760124599233181457239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49229013499465644241942985 36921760124599233181457239)
  ·
    refine ⟨55382640186898849772185859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36921760124599233181457239 55382640186898849772185859)
    ·
      refine ⟨83073960280348274658278789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55382640186898849772185859 83073960280348274658278789)
      ·
        refine ⟨15576367552565301498427273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83073960280348274658278789 15576367552565301498427273)
        ·
          refine ⟨11682275664423976123820455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15576367552565301498427273 11682275664423976123820455)
          ·
            refine ⟨17523413496635964185730683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11682275664423976123820455 17523413496635964185730683)
            ·
              refine ⟨26285120244953946278596025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17523413496635964185730683 26285120244953946278596025)
              ·
                refine ⟨19713840183715459708947019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26285120244953946278596025 19713840183715459708947019)
                ·
                  refine ⟨29570760275573189563420529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19713840183715459708947019 29570760275573189563420529)
                  ·
                    refine ⟨22178070206679892172565397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29570760275573189563420529 22178070206679892172565397)
                    ·
                      refine ⟨1039597040938119945589003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22178070206679892172565397 1039597040938119945589003)
                      ·
                        rfl

theorem cell23_2024608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2024608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024608 prefixEnd_2024608 := by exact prefixLift 2024608
  have htrace : WordTrace (prefixWord ++ tailWord_2024608) baseStart_2024608 baseEnd_2024608 := by
    simpa [prefixWord, tailWord_2024608, baseEnd_2024608] using wordTrace_append hprefix tailTrace_2024608
  have hstable : (prefixWord ++ tailWord_2024608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024608).length < 2 ^ (prefixWord ++ tailWord_2024608).sum := by decide
  have hdescent : baseEnd_2024608 < baseStart_2024608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024655 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 2, 6, 2]
def baseStart_2024655 : Nat := 118140960795 + 2024655 * 2 ^ 59
def prefixEnd_2024655 : Nat := 4983230072969 + 3 ^ 40 * 2024655 * 2
def baseEnd_2024655 : Nat := 1039621174528881261701287

theorem tailTrace_2024655 : CollatzResearch.WordTrace tailWord_2024655 prefixEnd_2024655 1039621174528881261701287 := by
  unfold tailWord_2024655
  simp only [CollatzResearch.WordTrace]
  refine ⟨73845234480028193389875419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49230156320018795593250279 73845234480028193389875419)
  ·
    refine ⟨110767851720042290084813129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73845234480028193389875419 110767851720042290084813129)
    ·
      refine ⟨83075888790031717563609847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110767851720042290084813129 83075888790031717563609847)
      ·
        refine ⟨124613833185047576345414771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83075888790031717563609847 124613833185047576345414771)
        ·
          refine ⟨186920749777571364518122157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124613833185047576345414771 186920749777571364518122157)
          ·
            refine ⟨70095281166589261694295809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186920749777571364518122157 70095281166589261694295809)
            ·
              refine ⟨52571460874941946270721857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70095281166589261694295809 52571460874941946270721857)
              ·
                refine ⟨39428595656206459703041393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52571460874941946270721857 39428595656206459703041393)
                ·
                  refine ⟨29571446742154844777281045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39428595656206459703041393 29571446742154844777281045)
                  ·
                    refine ⟨1386161566038508348935049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29571446742154844777281045 1386161566038508348935049)
                    ·
                      refine ⟨1039621174528881261701287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386161566038508348935049 1039621174528881261701287)
                      ·
                        rfl

theorem cell23_2024655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6, 2].length) (baseStart_2024655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024655 prefixEnd_2024655 := by exact prefixLift 2024655
  have htrace : WordTrace (prefixWord ++ tailWord_2024655) baseStart_2024655 baseEnd_2024655 := by
    simpa [prefixWord, tailWord_2024655, baseEnd_2024655] using wordTrace_append hprefix tailTrace_2024655
  have hstable : (prefixWord ++ tailWord_2024655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024655).length < 2 ^ (prefixWord ++ tailWord_2024655).sum := by decide
  have hdescent : baseEnd_2024655 < baseStart_2024655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024672 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4]
def baseStart_2024672 : Nat := 118140960795 + 2024672 * 2 ^ 59
def prefixEnd_2024672 : Nat := 4983230072969 + 3 ^ 40 * 2024672 * 2
def baseEnd_2024672 : Nat := 1039629903700007695188709

theorem tailTrace_2024672 : CollatzResearch.WordTrace tailWord_2024672 prefixEnd_2024672 1039629903700007695188709 := by
  unfold tailWord_2024672
  simp only [CollatzResearch.WordTrace]
  refine ⟨36922927260483302646622135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49230569680644403528829513 36922927260483302646622135)
  ·
    refine ⟨55384390890724953969933203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36922927260483302646622135 55384390890724953969933203)
    ·
      refine ⟨83076586336087430954899805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55384390890724953969933203 83076586336087430954899805)
      ·
        refine ⟨31153719876032786608087427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83076586336087430954899805 31153719876032786608087427)
        ·
          refine ⟨46730579814049179912131141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31153719876032786608087427 46730579814049179912131141)
          ·
            refine ⟨8761983715134221233524589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46730579814049179912131141 8761983715134221233524589)
            ·
              refine ⟨3285743893175332962571721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8761983715134221233524589 3285743893175332962571721)
              ·
                refine ⟨2464307919881499721928791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3285743893175332962571721 2464307919881499721928791)
                ·
                  refine ⟨3696461879822249582893187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464307919881499721928791 3696461879822249582893187)
                  ·
                    refine ⟨5544692819733374374339781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3696461879822249582893187 5544692819733374374339781)
                    ·
                      refine ⟨1039629903700007695188709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5544692819733374374339781 1039629903700007695188709)
                      ·
                        rfl

theorem cell23_2024672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_2024672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024672 prefixEnd_2024672 := by exact prefixLift 2024672
  have htrace : WordTrace (prefixWord ++ tailWord_2024672) baseStart_2024672 baseEnd_2024672 := by
    simpa [prefixWord, tailWord_2024672, baseEnd_2024672] using wordTrace_append hprefix tailTrace_2024672
  have hstable : (prefixWord ++ tailWord_2024672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024672).length < 2 ^ (prefixWord ++ tailWord_2024672).sum := by decide
  have hdescent : baseEnd_2024672 < baseStart_2024672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024700 : List Nat := [2, 2, 2, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_2024700 : Nat := 118140960795 + 2024700 * 2 ^ 59
def prefixEnd_2024700 : Nat := 4983230072969 + 3 ^ 40 * 2024700 * 2
def baseEnd_2024700 : Nat := 1039644281158333585638581

theorem tailTrace_2024700 : CollatzResearch.WordTrace tailWord_2024700 prefixEnd_2024700 1039644281158333585638581 := by
  unfold tailWord_2024700
  simp only [CollatzResearch.WordTrace]
  refine ⟨36923437882432583037631777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49231250509910110716842369 36923437882432583037631777)
  ·
    refine ⟨27692578411824437278223833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36923437882432583037631777 27692578411824437278223833)
    ·
      refine ⟨20769433808868327958667875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27692578411824437278223833 20769433808868327958667875)
      ·
        refine ⟨31154150713302491938001813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20769433808868327958667875 31154150713302491938001813)
        ·
          refine ⟨1460350814686054309593835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31154150713302491938001813 1460350814686054309593835)
          ·
            refine ⟨2190526222029081464390753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460350814686054309593835 2190526222029081464390753)
            ·
              refine ⟨1642894666521811098293065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190526222029081464390753 1642894666521811098293065)
              ·
                refine ⟨1232170999891358323719799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642894666521811098293065 1232170999891358323719799)
                ·
                  refine ⟨1848256499837037485579699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232170999891358323719799 1848256499837037485579699)
                  ·
                    refine ⟨2772384749755556228369549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848256499837037485579699 2772384749755556228369549)
                    ·
                      refine ⟨1039644281158333585638581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2772384749755556228369549 1039644281158333585638581)
                      ·
                        rfl

theorem cell23_2024700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_2024700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024700 prefixEnd_2024700 := by exact prefixLift 2024700
  have htrace : WordTrace (prefixWord ++ tailWord_2024700) baseStart_2024700 baseEnd_2024700 := by
    simpa [prefixWord, tailWord_2024700, baseEnd_2024700] using wordTrace_append hprefix tailTrace_2024700
  have hstable : (prefixWord ++ tailWord_2024700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024700).length < 2 ^ (prefixWord ++ tailWord_2024700).sum := by decide
  have hdescent : baseEnd_2024700 < baseStart_2024700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024712 : List Nat := [2, 1, 3, 2, 4, 2, 1, 8]
def baseStart_2024712 : Nat := 118140960795 + 2024712 * 2 ^ 59
def prefixEnd_2024712 : Nat := 4983230072969 + 3 ^ 40 * 2024712 * 2
def baseEnd_2024712 : Nat := 38505571960229168099575

theorem tailTrace_2024712 : CollatzResearch.WordTrace tailWord_2024712 prefixEnd_2024712 38505571960229168099575 := by
  unfold tailWord_2024712
  simp only [CollatzResearch.WordTrace]
  refine ⟨36923656720410846062350195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49231542293881128083133593 36923656720410846062350195)
  ·
    refine ⟨55385485080616269093525293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36923656720410846062350195 55385485080616269093525293)
    ·
      refine ⟨20769556905231100910071985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55385485080616269093525293 20769556905231100910071985)
      ·
        refine ⟨15577167678923325682553989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20769556905231100910071985 15577167678923325682553989)
        ·
          refine ⟨2920718939798123565478873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15577167678923325682553989 2920718939798123565478873)
          ·
            refine ⟨2190539204848592674109155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2920718939798123565478873 2190539204848592674109155)
            ·
              refine ⟨3285808807272889011163733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190539204848592674109155 3285808807272889011163733)
              ·
                refine ⟨38505571960229168099575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3285808807272889011163733 38505571960229168099575)
                ·
                  rfl

theorem cell23_2024712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 8].length) (baseStart_2024712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024712 prefixEnd_2024712 := by exact prefixLift 2024712
  have htrace : WordTrace (prefixWord ++ tailWord_2024712) baseStart_2024712 baseEnd_2024712 := by
    simpa [prefixWord, tailWord_2024712, baseEnd_2024712] using wordTrace_append hprefix tailTrace_2024712
  have hstable : (prefixWord ++ tailWord_2024712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024712).length < 2 ^ (prefixWord ++ tailWord_2024712).sum := by decide
  have hdescent : baseEnd_2024712 < baseStart_2024712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024755 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 2, 6]
def baseStart_2024755 : Nat := 118140960795 + 2024755 * 2 ^ 59
def prefixEnd_2024755 : Nat := 4983230072969 + 3 ^ 40 * 2024755 * 2
def baseEnd_2024755 : Nat := 346557507531443623483609

theorem tailTrace_2024755 : CollatzResearch.WordTrace tailWord_2024755 prefixEnd_2024755 346557507531443623483609 := by
  unfold tailWord_2024755
  simp only [CollatzResearch.WordTrace]
  refine ⟨73848881779665910468515719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49232587853110606979010479 73848881779665910468515719)
  ·
    refine ⟨110773322669498865702773579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73848881779665910468515719 110773322669498865702773579)
    ·
      refine ⟨166159984004248298554160369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110773322669498865702773579 166159984004248298554160369)
      ·
        refine ⟨124619988003186223915620277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166159984004248298554160369 124619988003186223915620277)
        ·
          refine ⟨11683123875298708492089401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124619988003186223915620277 11683123875298708492089401)
          ·
            refine ⟨8762342906474031369067051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11683123875298708492089401 8762342906474031369067051)
            ·
              refine ⟨13143514359711047053600577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8762342906474031369067051 13143514359711047053600577)
              ·
                refine ⟨9857635769783285290200433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13143514359711047053600577 9857635769783285290200433)
                ·
                  refine ⟨7393226827337463967650325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9857635769783285290200433 7393226827337463967650325)
                  ·
                    refine ⟨346557507531443623483609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7393226827337463967650325 346557507531443623483609)
                    ·
                      rfl

theorem cell23_2024755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 6].length) (baseStart_2024755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024755 prefixEnd_2024755 := by exact prefixLift 2024755
  have htrace : WordTrace (prefixWord ++ tailWord_2024755) baseStart_2024755 baseEnd_2024755 := by
    simpa [prefixWord, tailWord_2024755, baseEnd_2024755] using wordTrace_append hprefix tailTrace_2024755
  have hstable : (prefixWord ++ tailWord_2024755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024755).length < 2 ^ (prefixWord ++ tailWord_2024755).sum := by decide
  have hdescent : baseEnd_2024755 < baseStart_2024755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024785 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 7]
def baseStart_2024785 : Nat := 118140960795 + 2024785 * 2 ^ 59
def prefixEnd_2024785 : Nat := 4983230072969 + 3 ^ 40 * 2024785 * 2
def baseEnd_2024785 : Nat := 115520880779329528119521

theorem tailTrace_2024785 : CollatzResearch.WordTrace tailWord_2024785 prefixEnd_2024785 115520880779329528119521 := by
  unfold tailWord_2024785
  simp only [CollatzResearch.WordTrace]
  refine ⟨73849975969557225592107809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49233317313038150394738539 73849975969557225592107809)
  ·
    refine ⟨55387481977167919194080857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73849975969557225592107809 55387481977167919194080857)
    ·
      refine ⟨41540611482875939395560643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55387481977167919194080857 41540611482875939395560643)
      ·
        refine ⟨62310917224313909093340965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41540611482875939395560643 62310917224313909093340965)
        ·
          refine ⟨11683296979558857955001431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62310917224313909093340965 11683296979558857955001431)
          ·
            refine ⟨17524945469338286932502147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11683296979558857955001431 17524945469338286932502147)
            ·
              refine ⟨26287418204007430398753221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17524945469338286932502147 26287418204007430398753221)
              ·
                refine ⟨4928890913251393199766229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26287418204007430398753221 4928890913251393199766229)
                ·
                  refine ⟨115520880779329528119521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4928890913251393199766229 115520880779329528119521)
                  ·
                    rfl

theorem cell23_2024785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 7].length) (baseStart_2024785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024785 prefixEnd_2024785 := by exact prefixLift 2024785
  have htrace : WordTrace (prefixWord ++ tailWord_2024785) baseStart_2024785 baseEnd_2024785 := by
    simpa [prefixWord, tailWord_2024785, baseEnd_2024785] using wordTrace_append hprefix tailTrace_2024785
  have hstable : (prefixWord ++ tailWord_2024785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024785).length < 2 ^ (prefixWord ++ tailWord_2024785).sum := by decide
  have hdescent : baseEnd_2024785 < baseStart_2024785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024825 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2024825 : Nat := 118140960795 + 2024825 * 2 ^ 59
def prefixEnd_2024825 : Nat := 4983230072969 + 3 ^ 40 * 2024825 * 2
def baseEnd_2024825 : Nat := 1039708466240145596575505

theorem tailTrace_2024825 : CollatzResearch.WordTrace tailWord_2024825 prefixEnd_2024825 1039708466240145596575505 := by
  unfold tailWord_2024825
  simp only [CollatzResearch.WordTrace]
  refine ⟨73851434889412312423563929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49234289926274874949042619 73851434889412312423563929)
  ·
    refine ⟨55388576167059234317672947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73851434889412312423563929 55388576167059234317672947)
    ·
      refine ⟨83082864250588851476509421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55388576167059234317672947 83082864250588851476509421)
      ·
        refine ⟨31156074093970819303691033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83082864250588851476509421 31156074093970819303691033)
        ·
          refine ⟨23367055570478114477768275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31156074093970819303691033 23367055570478114477768275)
          ·
            refine ⟨35050583355717171716652413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23367055570478114477768275 35050583355717171716652413)
            ·
              refine ⟨13143968758393939393744655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35050583355717171716652413 13143968758393939393744655)
              ·
                refine ⟨19715953137590909090616983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13143968758393939393744655 19715953137590909090616983)
                ·
                  refine ⟨29573929706386363635925475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19715953137590909090616983 29573929706386363635925475)
                  ·
                    refine ⟨44360894559579545453888213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29573929706386363635925475 44360894559579545453888213)
                    ·
                      refine ⟨1039708466240145596575505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44360894559579545453888213 1039708466240145596575505)
                      ·
                        rfl

theorem cell23_2024825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2024825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024825 prefixEnd_2024825 := by exact prefixLift 2024825
  have htrace : WordTrace (prefixWord ++ tailWord_2024825) baseStart_2024825 baseEnd_2024825 := by
    simpa [prefixWord, tailWord_2024825, baseEnd_2024825] using wordTrace_append hprefix tailTrace_2024825
  have hstable : (prefixWord ++ tailWord_2024825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024825).length < 2 ^ (prefixWord ++ tailWord_2024825).sum := by decide
  have hdescent : baseEnd_2024825 < baseStart_2024825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024906 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_2024906 : Nat := 118140960795 + 2024906 * 2 ^ 59
def prefixEnd_2024906 : Nat := 4983230072969 + 3 ^ 40 * 2024906 * 2
def baseEnd_2024906 : Nat := 1039750058173159779662633

theorem tailTrace_2024906 : CollatzResearch.WordTrace tailWord_2024906 prefixEnd_2024906 1039750058173159779662633 := by
  unfold tailWord_2024906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18463597300529715814315643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49236259468079242171508381 18463597300529715814315643)
  ·
    refine ⟨27695395950794573721473465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18463597300529715814315643 27695395950794573721473465)
    ·
      refine ⟨20771546963095930291105099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27695395950794573721473465 20771546963095930291105099)
      ·
        refine ⟨31157320444643895436657649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20771546963095930291105099 31157320444643895436657649)
        ·
          refine ⟨23367990333482921577493237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31157320444643895436657649 23367990333482921577493237)
          ·
            refine ⟨2190749093764023897889991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23367990333482921577493237 2190749093764023897889991)
            ·
              refine ⟨3286123640646035846834987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190749093764023897889991 3286123640646035846834987)
              ·
                refine ⟨4929185460969053770252481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286123640646035846834987 4929185460969053770252481)
                ·
                  refine ⟨3696889095726790327689361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929185460969053770252481 3696889095726790327689361)
                  ·
                    refine ⟨2772666821795092745767021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3696889095726790327689361 2772666821795092745767021)
                    ·
                      refine ⟨1039750058173159779662633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2772666821795092745767021 1039750058173159779662633)
                      ·
                        rfl

theorem cell23_2024906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_2024906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024906 prefixEnd_2024906 := by exact prefixLift 2024906
  have htrace : WordTrace (prefixWord ++ tailWord_2024906) baseStart_2024906 baseEnd_2024906 := by
    simpa [prefixWord, tailWord_2024906, baseEnd_2024906] using wordTrace_append hprefix tailTrace_2024906
  have hstable : (prefixWord ++ tailWord_2024906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024906).length < 2 ^ (prefixWord ++ tailWord_2024906).sum := by decide
  have hdescent : baseEnd_2024906 < baseStart_2024906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024936 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2024936 : Nat := 118140960795 + 2024936 * 2 ^ 59
def prefixEnd_2024936 : Nat := 4983230072969 + 3 ^ 40 * 2024936 * 2
def baseEnd_2024936 : Nat := 1039765462592794662287495

theorem tailTrace_2024936 : CollatzResearch.WordTrace tailWord_2024936 prefixEnd_2024936 1039765462592794662287495 := by
  unfold tailWord_2024936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36927741696005089190427331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49236988928006785587236441 36927741696005089190427331)
  ·
    refine ⟨55391612544007633785640997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36927741696005089190427331 55391612544007633785640997)
    ·
      refine ⟨10385927352001431334807687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55391612544007633785640997 10385927352001431334807687)
      ·
        refine ⟨15578891028002147002211531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10385927352001431334807687 15578891028002147002211531)
        ·
          refine ⟨23368336542003220503317297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15578891028002147002211531 23368336542003220503317297)
          ·
            refine ⟨17526252406502415377487973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23368336542003220503317297 17526252406502415377487973)
            ·
              refine ⟨3286172326219202883278995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17526252406502415377487973 3286172326219202883278995)
              ·
                refine ⟨4929258489328804324918493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286172326219202883278995 4929258489328804324918493)
                ·
                  refine ⟨1848471933498301621844435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4929258489328804324918493 1848471933498301621844435)
                  ·
                    refine ⟨2772707900247452432766653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848471933498301621844435 2772707900247452432766653)
                    ·
                      refine ⟨1039765462592794662287495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2772707900247452432766653 1039765462592794662287495)
                      ·
                        rfl

theorem cell23_2024936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2024936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024936 prefixEnd_2024936 := by exact prefixLift 2024936
  have htrace : WordTrace (prefixWord ++ tailWord_2024936) baseStart_2024936 baseEnd_2024936 := by
    simpa [prefixWord, tailWord_2024936, baseEnd_2024936] using wordTrace_append hprefix tailTrace_2024936
  have hstable : (prefixWord ++ tailWord_2024936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024936).length < 2 ^ (prefixWord ++ tailWord_2024936).sum := by decide
  have hdescent : baseEnd_2024936 < baseStart_2024936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024946 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2024946 : Nat := 118140960795 + 2024946 * 2 ^ 59
def prefixEnd_2024946 : Nat := 4983230072969 + 3 ^ 40 * 2024946 * 2
def baseEnd_2024946 : Nat := 1039770597399339623162449

theorem tailTrace_2024946 : CollatzResearch.WordTrace tailWord_2024946 prefixEnd_2024946 1039770597399339623162449 := by
  unfold tailWord_2024946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18463962030493487522179673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49237232081315966725812461 18463962030493487522179673)
  ·
    refine ⟨13847971522870115641634755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18463962030493487522179673 13847971522870115641634755)
    ·
      refine ⟨20771957284305173462452133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13847971522870115641634755 20771957284305173462452133)
      ·
        refine ⟨3894741990807220024209775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20771957284305173462452133 3894741990807220024209775)
        ·
          refine ⟨5842112986210830036314663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894741990807220024209775 5842112986210830036314663)
          ·
            refine ⟨8763169479316245054471995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842112986210830036314663 8763169479316245054471995)
            ·
              refine ⟨13144754218974367581707993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8763169479316245054471995 13144754218974367581707993)
              ·
                refine ⟨9858565664230775686280995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13144754218974367581707993 9858565664230775686280995)
                ·
                  refine ⟨14787848496346163529421493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9858565664230775686280995 14787848496346163529421493)
                  ·
                    refine ⟨1386360796532452830883265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14787848496346163529421493 1386360796532452830883265)
                    ·
                      refine ⟨1039770597399339623162449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386360796532452830883265 1039770597399339623162449)
                      ·
                        rfl

theorem cell23_2024946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2024946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024946 prefixEnd_2024946 := by exact prefixLift 2024946
  have htrace : WordTrace (prefixWord ++ tailWord_2024946) baseStart_2024946 baseEnd_2024946 := by
    simpa [prefixWord, tailWord_2024946, baseEnd_2024946] using wordTrace_append hprefix tailTrace_2024946
  have hstable : (prefixWord ++ tailWord_2024946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024946).length < 2 ^ (prefixWord ++ tailWord_2024946).sum := by decide
  have hdescent : baseEnd_2024946 < baseStart_2024946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024970 : List Nat := [3, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_2024970 : Nat := 118140960795 + 2024970 * 2 ^ 59
def prefixEnd_2024970 : Nat := 4983230072969 + 3 ^ 40 * 2024970 * 2
def baseEnd_2024970 : Nat := 1039782920935047529262339

theorem tailTrace_2024970 : CollatzResearch.WordTrace tailWord_2024970 prefixEnd_2024970 1039782920935047529262339 := by
  unfold tailWord_2024970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18464180868471750546898091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49237815649258001458394909 18464180868471750546898091)
  ·
    refine ⟨27696271302707625820347137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18464180868471750546898091 27696271302707625820347137)
    ·
      refine ⟨20772203477030719365260353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27696271302707625820347137 20772203477030719365260353)
      ·
        refine ⟨15579152607773039523945265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20772203477030719365260353 15579152607773039523945265)
        ·
          refine ⟨11684364455829779642958949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15579152607773039523945265 11684364455829779642958949)
          ·
            refine ⟨2190818335468083683054803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11684364455829779642958949 2190818335468083683054803)
            ·
              refine ⟨3286227503202125524582205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190818335468083683054803 3286227503202125524582205)
              ·
                refine ⟨1232335313700797071718327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3286227503202125524582205 1232335313700797071718327)
                ·
                  refine ⟨1848502970551195607577491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232335313700797071718327 1848502970551195607577491)
                  ·
                    refine ⟨2772754455826793411366237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848502970551195607577491 2772754455826793411366237)
                    ·
                      refine ⟨1039782920935047529262339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2772754455826793411366237 1039782920935047529262339)
                      ·
                        rfl

theorem cell23_2024970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_2024970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024970 prefixEnd_2024970 := by exact prefixLift 2024970
  have htrace : WordTrace (prefixWord ++ tailWord_2024970) baseStart_2024970 baseEnd_2024970 := by
    simpa [prefixWord, tailWord_2024970, baseEnd_2024970] using wordTrace_append hprefix tailTrace_2024970
  have hstable : (prefixWord ++ tailWord_2024970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024970).length < 2 ^ (prefixWord ++ tailWord_2024970).sum := by decide
  have hdescent : baseEnd_2024970 < baseStart_2024970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024979 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 5]
def baseStart_2024979 : Nat := 118140960795 + 2024979 * 2 ^ 59
def prefixEnd_2024979 : Nat := 4983230072969 + 3 ^ 40 * 2024979 * 2
def baseEnd_2024979 : Nat := 1039787542260937994049797

theorem tailTrace_2024979 : CollatzResearch.WordTrace tailWord_2024979 prefixEnd_2024979 1039787542260937994049797 := by
  unfold tailWord_2024979
  simp only [CollatzResearch.WordTrace]
  refine ⟨73857051730854396724669991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49238034487236264483113327 73857051730854396724669991)
  ·
    refine ⟨110785577596281595087004987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73857051730854396724669991 110785577596281595087004987)
    ·
      refine ⟨166178366394422392630507481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110785577596281595087004987 166178366394422392630507481)
      ·
        refine ⟨124633774795816794472880611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166178366394422392630507481 124633774795816794472880611)
        ·
          refine ⟨186950662193725191709320917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124633774795816794472880611 186950662193725191709320917)
          ·
            refine ⟨4381656145165434180687209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 186950662193725191709320917 4381656145165434180687209)
            ·
              refine ⟨3286242108874075635515407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4381656145165434180687209 3286242108874075635515407)
              ·
                refine ⟨4929363163311113453273111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286242108874075635515407 4929363163311113453273111)
                ·
                  refine ⟨7394044744966670179909667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929363163311113453273111 7394044744966670179909667)
                  ·
                    refine ⟨11091067117450005269864501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394044744966670179909667 11091067117450005269864501)
                    ·
                      refine ⟨1039787542260937994049797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11091067117450005269864501 1039787542260937994049797)
                      ·
                        rfl

theorem cell23_2024979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_2024979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024979 prefixEnd_2024979 := by exact prefixLift 2024979
  have htrace : WordTrace (prefixWord ++ tailWord_2024979) baseStart_2024979 baseEnd_2024979 := by
    simpa [prefixWord, tailWord_2024979, baseEnd_2024979] using wordTrace_append hprefix tailTrace_2024979
  have hstable : (prefixWord ++ tailWord_2024979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024979).length < 2 ^ (prefixWord ++ tailWord_2024979).sum := by decide
  have hdescent : baseEnd_2024979 < baseStart_2024979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024980 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2024980 : Nat := 118140960795 + 2024980 * 2 ^ 59
def prefixEnd_2024980 : Nat := 4983230072969 + 3 ^ 40 * 2024980 * 2
def baseEnd_2024980 : Nat := 1039788055741592490137293

theorem tailTrace_2024980 : CollatzResearch.WordTrace tailWord_2024980 prefixEnd_2024980 1039788055741592490137293 := by
  unfold tailWord_2024980
  simp only [CollatzResearch.WordTrace]
  refine ⟨36928544101925386947728197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49238058802567182596970929 36928544101925386947728197)
  ·
    refine ⟨6924102019111010052699037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36928544101925386947728197 6924102019111010052699037)
    ·
      refine ⟨2596538257166628769762139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6924102019111010052699037 2596538257166628769762139)
      ·
        refine ⟨3894807385749943154643209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2596538257166628769762139 3894807385749943154643209)
        ·
          refine ⟨2921105539312457365982407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3894807385749943154643209 2921105539312457365982407)
          ·
            refine ⟨4381658308968686048973611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921105539312457365982407 4381658308968686048973611)
            ·
              refine ⟨6572487463453029073460417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381658308968686048973611 6572487463453029073460417)
              ·
                refine ⟨4929365597589771805095313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6572487463453029073460417 4929365597589771805095313)
                ·
                  refine ⟨3697024198192328853821485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4929365597589771805095313 3697024198192328853821485)
                  ·
                    refine ⟨1386384074322123320183057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697024198192328853821485 1386384074322123320183057)
                    ·
                      refine ⟨1039788055741592490137293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386384074322123320183057 1039788055741592490137293)
                      ·
                        rfl

theorem cell23_2024980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2024980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024980 prefixEnd_2024980 := by exact prefixLift 2024980
  have htrace : WordTrace (prefixWord ++ tailWord_2024980) baseStart_2024980 baseEnd_2024980 := by
    simpa [prefixWord, tailWord_2024980, baseEnd_2024980] using wordTrace_append hprefix tailTrace_2024980
  have hstable : (prefixWord ++ tailWord_2024980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024980).length < 2 ^ (prefixWord ++ tailWord_2024980).sum := by decide
  have hdescent : baseEnd_2024980 < baseStart_2024980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2024993 : List Nat := [1, 2, 3, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_2024993 : Nat := 118140960795 + 2024993 * 2 ^ 59
def prefixEnd_2024993 : Nat := 4983230072969 + 3 ^ 40 * 2024993 * 2
def baseEnd_2024993 : Nat := 1039794730990100939274733

theorem tailTrace_2024993 : CollatzResearch.WordTrace tailWord_2024993 prefixEnd_2024993 1039794730990100939274733 := by
  unfold tailWord_2024993
  simp only [CollatzResearch.WordTrace]
  refine ⟨73857562352803677115679633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49238374901869118077119755 73857562352803677115679633)
  ·
    refine ⟨55393171764602757836759725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73857562352803677115679633 55393171764602757836759725)
    ·
      refine ⟨20772439411726034188784897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55393171764602757836759725 20772439411726034188784897)
      ·
        refine ⟨15579329558794525641588673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20772439411726034188784897 15579329558794525641588673)
        ·
          refine ⟨11684497169095894231191505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15579329558794525641588673 11684497169095894231191505)
          ·
            refine ⟨8763372876821920673393629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11684497169095894231191505 8763372876821920673393629)
            ·
              refine ⟨3286264828808220252522611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8763372876821920673393629 3286264828808220252522611)
              ·
                refine ⟨4929397243212330378783917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286264828808220252522611 4929397243212330378783917)
                ·
                  refine ⟨1848523966204623892043969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4929397243212330378783917 1848523966204623892043969)
                  ·
                    refine ⟨1386392974653467919032977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1848523966204623892043969 1386392974653467919032977)
                    ·
                      refine ⟨1039794730990100939274733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386392974653467919032977 1039794730990100939274733)
                      ·
                        rfl

theorem cell23_2024993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_2024993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2024993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2024993 prefixEnd_2024993 := by exact prefixLift 2024993
  have htrace : WordTrace (prefixWord ++ tailWord_2024993) baseStart_2024993 baseEnd_2024993 := by
    simpa [prefixWord, tailWord_2024993, baseEnd_2024993] using wordTrace_append hprefix tailTrace_2024993
  have hstable : (prefixWord ++ tailWord_2024993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2024993).length < 2 ^ (prefixWord ++ tailWord_2024993).sum := by decide
  have hdescent : baseEnd_2024993 < baseStart_2024993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2024993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025009 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_2025009 : Nat := 118140960795 + 2025009 * 2 ^ 59
def prefixEnd_2025009 : Nat := 4983230072969 + 3 ^ 40 * 2025009 * 2
def baseEnd_2025009 : Nat := 1039802946680572876674659

theorem tailTrace_2025009 : CollatzResearch.WordTrace tailWord_2025009 prefixEnd_2025009 1039802946680572876674659 := by
  unfold tailWord_2025009
  simp only [CollatzResearch.WordTrace]
  refine ⟨73858145920745711848262081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49238763947163807898841387 73858145920745711848262081)
  ·
    refine ⟨55393609440559283886196561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73858145920745711848262081 55393609440559283886196561)
    ·
      refine ⟨41545207080419462914647421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55393609440559283886196561 41545207080419462914647421)
      ·
        refine ⟨15579452655157298592992783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41545207080419462914647421 15579452655157298592992783)
        ·
          refine ⟨23369178982735947889489175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579452655157298592992783 23369178982735947889489175)
          ·
            refine ⟨35053768474103921834233763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23369178982735947889489175 35053768474103921834233763)
            ·
              refine ⟨52580652711155882751350645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35053768474103921834233763 52580652711155882751350645)
              ·
                refine ⟨4929436191670864007939123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52580652711155882751350645 4929436191670864007939123)
                ·
                  refine ⟨7394154287506296011908685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929436191670864007939123 7394154287506296011908685)
                  ·
                    refine ⟨2772807857814861004465757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7394154287506296011908685 2772807857814861004465757)
                    ·
                      refine ⟨1039802946680572876674659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2772807857814861004465757 1039802946680572876674659)
                      ·
                        rfl

theorem cell23_2025009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_2025009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025009 prefixEnd_2025009 := by exact prefixLift 2025009
  have htrace : WordTrace (prefixWord ++ tailWord_2025009) baseStart_2025009 baseEnd_2025009 := by
    simpa [prefixWord, tailWord_2025009, baseEnd_2025009] using wordTrace_append hprefix tailTrace_2025009
  have hstable : (prefixWord ++ tailWord_2025009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025009).length < 2 ^ (prefixWord ++ tailWord_2025009).sum := by decide
  have hdescent : baseEnd_2025009 < baseStart_2025009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025013 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_2025013 : Nat := 118140960795 + 2025013 * 2 ^ 59
def prefixEnd_2025013 : Nat := 4983230072969 + 3 ^ 40 * 2025013 * 2
def baseEnd_2025013 : Nat := 1039805000603190861024641

theorem tailTrace_2025013 : CollatzResearch.WordTrace tailWord_2025013 prefixEnd_2025013 1039805000603190861024641 := by
  unfold tailWord_2025013
  simp only [CollatzResearch.WordTrace]
  refine ⟨73858291812731220531407693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49238861208487480354271795 73858291812731220531407693)
  ·
    refine ⟨27696859429774207699277885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73858291812731220531407693 27696859429774207699277885)
    ·
      refine ⟨10386322286165327887229207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27696859429774207699277885 10386322286165327887229207)
      ·
        refine ⟨15579483429247991830843811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10386322286165327887229207 15579483429247991830843811)
        ·
          refine ⟨23369225143871987746265717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579483429247991830843811 23369225143871987746265717)
          ·
            refine ⟨2190864857237998851212411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23369225143871987746265717 2190864857237998851212411)
            ·
              refine ⟨3286297285856998276818617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190864857237998851212411 3286297285856998276818617)
              ·
                refine ⟨2464722964392748707613963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286297285856998276818617 2464722964392748707613963)
                ·
                  refine ⟨3697084446589123061420945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2464722964392748707613963 3697084446589123061420945)
                  ·
                    refine ⟨2772813334941842296065709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697084446589123061420945 2772813334941842296065709)
                    ·
                      refine ⟨1039805000603190861024641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2772813334941842296065709 1039805000603190861024641)
                      ·
                        rfl

theorem cell23_2025013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_2025013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025013 prefixEnd_2025013 := by exact prefixLift 2025013
  have htrace : WordTrace (prefixWord ++ tailWord_2025013) baseStart_2025013 baseEnd_2025013 := by
    simpa [prefixWord, tailWord_2025013, baseEnd_2025013] using wordTrace_append hprefix tailTrace_2025013
  have hstable : (prefixWord ++ tailWord_2025013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025013).length < 2 ^ (prefixWord ++ tailWord_2025013).sum := by decide
  have hdescent : baseEnd_2025013 < baseStart_2025013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025030 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2025030 : Nat := 118140960795 + 2025030 * 2 ^ 59
def prefixEnd_2025030 : Nat := 4983230072969 + 3 ^ 40 * 2025030 * 2
def baseEnd_2025030 : Nat := 1039813729774317294512063

theorem tailTrace_2025030 : CollatzResearch.WordTrace tailWord_2025030 prefixEnd_2025030 1039813729774317294512063 := by
  unfold tailWord_2025030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308090995427176013586767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49239274569113088289851029 2308090995427176013586767)
  ·
    refine ⟨3462136493140764020380151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308090995427176013586767 3462136493140764020380151)
    ·
      refine ⟨5193204739711146030570227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462136493140764020380151 5193204739711146030570227)
      ·
        refine ⟨7789807109566719045855341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5193204739711146030570227 7789807109566719045855341)
        ·
          refine ⟨2921177666087519642195753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7789807109566719045855341 2921177666087519642195753)
          ·
            refine ⟨2190883249565639731646815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2921177666087519642195753 2190883249565639731646815)
            ·
              refine ⟨3286324874348459597470223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190883249565639731646815 3286324874348459597470223)
              ·
                refine ⟨4929487311522689396205335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286324874348459597470223 4929487311522689396205335)
                ·
                  refine ⟨7394230967284034094308003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4929487311522689396205335 7394230967284034094308003)
                  ·
                    refine ⟨11091346450926051141462005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7394230967284034094308003 11091346450926051141462005)
                    ·
                      refine ⟨1039813729774317294512063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11091346450926051141462005 1039813729774317294512063)
                      ·
                        rfl

theorem cell23_2025030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2025030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025030 prefixEnd_2025030 := by exact prefixLift 2025030
  have htrace : WordTrace (prefixWord ++ tailWord_2025030) baseStart_2025030 baseEnd_2025030 := by
    simpa [prefixWord, tailWord_2025030, baseEnd_2025030] using wordTrace_append hprefix tailTrace_2025030
  have hstable : (prefixWord ++ tailWord_2025030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025030).length < 2 ^ (prefixWord ++ tailWord_2025030).sum := by decide
  have hdescent : baseEnd_2025030 < baseStart_2025030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025059 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 2, 6]
def baseStart_2025059 : Nat := 118140960795 + 2025059 * 2 ^ 59
def prefixEnd_2025059 : Nat := 4983230072969 + 3 ^ 40 * 2025059 * 2
def baseEnd_2025059 : Nat := 346609540237765893683143

theorem tailTrace_2025059 : CollatzResearch.WordTrace tailWord_2025059 prefixEnd_2025059 346609540237765893683143 := by
  unfold tailWord_2025059
  simp only [CollatzResearch.WordTrace]
  refine ⟨73859969570564570387582231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49239979713709713591721487 73859969570564570387582231)
  ·
    refine ⟨110789954355846855581373347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73859969570564570387582231 110789954355846855581373347)
    ·
      refine ⟨166184931533770283372060021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110789954355846855581373347 166184931533770283372060021)
      ·
        refine ⟨15579837331290964066130627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166184931533770283372060021 15579837331290964066130627)
        ·
          refine ⟨23369755996936446099195941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15579837331290964066130627 23369755996936446099195941)
          ·
            refine ⟨4381829249425583643599239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23369755996936446099195941 4381829249425583643599239)
            ·
              refine ⟨6572743874138375465398859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4381829249425583643599239 6572743874138375465398859)
              ·
                refine ⟨9859115811207563198098289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6572743874138375465398859 9859115811207563198098289)
                ·
                  refine ⟨7394336858405672398573717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9859115811207563198098289 7394336858405672398573717)
                  ·
                    refine ⟨346609540237765893683143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7394336858405672398573717 346609540237765893683143)
                    ·
                      rfl

theorem cell23_2025059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 6].length) (baseStart_2025059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025059 prefixEnd_2025059 := by exact prefixLift 2025059
  have htrace : WordTrace (prefixWord ++ tailWord_2025059) baseStart_2025059 baseEnd_2025059 := by
    simpa [prefixWord, tailWord_2025059, baseEnd_2025059] using wordTrace_append hprefix tailTrace_2025059
  have hstable : (prefixWord ++ tailWord_2025059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025059).length < 2 ^ (prefixWord ++ tailWord_2025059).sum := by decide
  have hdescent : baseEnd_2025059 < baseStart_2025059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025099 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 3]
def baseStart_2025099 : Nat := 118140960795 + 2025099 * 2 ^ 59
def prefixEnd_2025099 : Nat := 4983230072969 + 3 ^ 40 * 2025099 * 2
def baseEnd_2025099 : Nat := 1039849159939477524549245

theorem tailTrace_2025099 : CollatzResearch.WordTrace tailWord_2025099 prefixEnd_2025099 1039849159939477524549245 := by
  unfold tailWord_2025099
  simp only [CollatzResearch.WordTrace]
  refine ⟨73861428490419657219038351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49240952326946438146025567 73861428490419657219038351)
  ·
    refine ⟨110792142735629485828557527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73861428490419657219038351 110792142735629485828557527)
    ·
      refine ⟨166188214103444228742836291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110792142735629485828557527 166188214103444228742836291)
      ·
        refine ⟨249282321155166343114254437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166188214103444228742836291 249282321155166343114254437)
        ·
          refine ⟨46740435216593689333922707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249282321155166343114254437 46740435216593689333922707)
          ·
            refine ⟨70110652824890534000884061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46740435216593689333922707 70110652824890534000884061)
            ·
              refine ⟨26291494809333950250331523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70110652824890534000884061 26291494809333950250331523)
              ·
                refine ⟨39437242214000925375497285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26291494809333950250331523 39437242214000925375497285)
                ·
                  refine ⟨7394482915125173507905741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39437242214000925375497285 7394482915125173507905741)
                  ·
                    refine ⟨2772931093171940065464653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7394482915125173507905741 2772931093171940065464653)
                    ·
                      refine ⟨1039849159939477524549245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2772931093171940065464653 1039849159939477524549245)
                      ·
                        rfl

theorem cell23_2025099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 3].length) (baseStart_2025099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025099 prefixEnd_2025099 := by exact prefixLift 2025099
  have htrace : WordTrace (prefixWord ++ tailWord_2025099) baseStart_2025099 baseEnd_2025099 := by
    simpa [prefixWord, tailWord_2025099, baseEnd_2025099] using wordTrace_append hprefix tailTrace_2025099
  have hstable : (prefixWord ++ tailWord_2025099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025099).length < 2 ^ (prefixWord ++ tailWord_2025099).sum := by decide
  have hdescent : baseEnd_2025099 < baseStart_2025099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025139 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4]
def baseStart_2025139 : Nat := 118140960795 + 2025139 * 2 ^ 59
def prefixEnd_2025139 : Nat := 4983230072969 + 3 ^ 40 * 2025139 * 2
def baseEnd_2025139 : Nat := 1039869699165657368049061

theorem tailTrace_2025139 : CollatzResearch.WordTrace tailWord_2025139 prefixEnd_2025139 1039869699165657368049061 := by
  unfold tailWord_2025139
  simp only [CollatzResearch.WordTrace]
  refine ⟨73862887410274744050494471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49241924940183162700329647 73862887410274744050494471)
  ·
    refine ⟨110794331115412116075741707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73862887410274744050494471 110794331115412116075741707)
    ·
      refine ⟨166191496673118174113612561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110794331115412116075741707 166191496673118174113612561)
      ·
        refine ⟨124643622504838630585209421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166191496673118174113612561 124643622504838630585209421)
        ·
          refine ⟨46741358439314486469453533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124643622504838630585209421 46741358439314486469453533)
          ·
            refine ⟨17528009414742932426045075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46741358439314486469453533 17528009414742932426045075)
            ·
              refine ⟨26292014122114398639067613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17528009414742932426045075 26292014122114398639067613)
              ·
                refine ⟨9859505295792899489650355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26292014122114398639067613 9859505295792899489650355)
                ·
                  refine ⟨14789257943689349234475533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9859505295792899489650355 14789257943689349234475533)
                  ·
                    refine ⟨5545971728883505962928325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14789257943689349234475533 5545971728883505962928325)
                    ·
                      refine ⟨1039869699165657368049061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5545971728883505962928325 1039869699165657368049061)
                      ·
                        rfl

theorem cell23_2025139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_2025139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025139 prefixEnd_2025139 := by exact prefixLift 2025139
  have htrace : WordTrace (prefixWord ++ tailWord_2025139) baseStart_2025139 baseEnd_2025139 := by
    simpa [prefixWord, tailWord_2025139, baseEnd_2025139] using wordTrace_append hprefix tailTrace_2025139
  have hstable : (prefixWord ++ tailWord_2025139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025139).length < 2 ^ (prefixWord ++ tailWord_2025139).sum := by decide
  have hdescent : baseEnd_2025139 < baseStart_2025139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025176 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 4, 2, 3]
def baseStart_2025176 : Nat := 118140960795 + 2025176 * 2 ^ 59
def prefixEnd_2025176 : Nat := 4983230072969 + 3 ^ 40 * 2025176 * 2
def baseEnd_2025176 : Nat := 1039888697949873723286391

theorem tailTrace_2025176 : CollatzResearch.WordTrace tailWord_2025176 prefixEnd_2025176 1039888697949873723286391 := by
  unfold tailWord_2025176
  simp only [CollatzResearch.WordTrace]
  refine ⟨36932118455570349684795691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49242824607427132913060921 36932118455570349684795691)
  ·
    refine ⟨55398177683355524527193537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36932118455570349684795691 55398177683355524527193537)
    ·
      refine ⟨41548633262516643395395153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55398177683355524527193537 41548633262516643395395153)
      ·
        refine ⟨31161474946887482546546365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41548633262516643395395153 31161474946887482546546365)
        ·
          refine ⟨11685553105082805954954887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31161474946887482546546365 11685553105082805954954887)
          ·
            refine ⟨17528329657624208932432331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11685553105082805954954887 17528329657624208932432331)
            ·
              refine ⟨26292494486436313398648497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17528329657624208932432331 26292494486436313398648497)
              ·
                refine ⟨19719370864827235048986373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26292494486436313398648497 19719370864827235048986373)
                ·
                  refine ⟨3697382037155106571684945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19719370864827235048986373 3697382037155106571684945)
                  ·
                    refine ⟨2773036527866329928763709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697382037155106571684945 2773036527866329928763709)
                    ·
                      refine ⟨1039888697949873723286391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2773036527866329928763709 1039888697949873723286391)
                      ·
                        rfl

theorem cell23_2025176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_2025176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025176 prefixEnd_2025176 := by exact prefixLift 2025176
  have htrace : WordTrace (prefixWord ++ tailWord_2025176) baseStart_2025176 baseEnd_2025176 := by
    simpa [prefixWord, tailWord_2025176, baseEnd_2025176] using wordTrace_append hprefix tailTrace_2025176
  have hstable : (prefixWord ++ tailWord_2025176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025176).length < 2 ^ (prefixWord ++ tailWord_2025176).sum := by decide
  have hdescent : baseEnd_2025176 < baseStart_2025176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025226 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_2025226 : Nat := 118140960795 + 2025226 * 2 ^ 59
def prefixEnd_2025226 : Nat := 4983230072969 + 3 ^ 40 * 2025226 * 2
def baseEnd_2025226 : Nat := 346638123994199509220387

theorem tailTrace_2025226 : CollatzResearch.WordTrace tailWord_2025226 prefixEnd_2025226 346638123994199509220387 := by
  unfold tailWord_2025226
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466515140239889477227883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49244040373973038605941021 18466515140239889477227883)
  ·
    refine ⟨27699772710359834215841825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18466515140239889477227883 27699772710359834215841825)
    ·
      refine ⟨20774829532769875661881369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27699772710359834215841825 20774829532769875661881369)
      ·
        refine ⟨15581122149577406746411027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20774829532769875661881369 15581122149577406746411027)
        ·
          refine ⟨23371683224366110119616541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581122149577406746411027 23371683224366110119616541)
          ·
            refine ⟨8764381209137291294856203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23371683224366110119616541 8764381209137291294856203)
            ·
              refine ⟨13146571813705936942284305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764381209137291294856203 13146571813705936942284305)
              ·
                refine ⟨9859928860279452706713229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13146571813705936942284305 9859928860279452706713229)
                ·
                  refine ⟨3697473322604794765017461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9859928860279452706713229 3697473322604794765017461)
                  ·
                    refine ⟨346638123994199509220387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3697473322604794765017461 346638123994199509220387)
                    ·
                      rfl

theorem cell23_2025226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_2025226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025226 prefixEnd_2025226 := by exact prefixLift 2025226
  have htrace : WordTrace (prefixWord ++ tailWord_2025226) baseStart_2025226 baseEnd_2025226 := by
    simpa [prefixWord, tailWord_2025226, baseEnd_2025226] using wordTrace_append hprefix tailTrace_2025226
  have hstable : (prefixWord ++ tailWord_2025226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025226).length < 2 ^ (prefixWord ++ tailWord_2025226).sum := by decide
  have hdescent : baseEnd_2025226 < baseStart_2025226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025260 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_2025260 : Nat := 118140960795 + 2025260 * 2 ^ 59
def prefixEnd_2025260 : Nat := 4983230072969 + 3 ^ 40 * 2025260 * 2
def baseEnd_2025260 : Nat := 346643943441617131545335

theorem tailTrace_2025260 : CollatzResearch.WordTrace tailWord_2025260 prefixEnd_2025260 346643943441617131545335 := by
  unfold tailWord_2025260
  simp only [CollatzResearch.WordTrace]
  refine ⟨36933650321418190857824617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49244867095224254477099489 36933650321418190857824617)
  ·
    refine ⟨27700237741063643143368463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36933650321418190857824617 27700237741063643143368463)
    ·
      refine ⟨41550356611595464715052695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27700237741063643143368463 41550356611595464715052695)
      ·
        refine ⟨62325534917393197072579043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41550356611595464715052695 62325534917393197072579043)
        ·
          refine ⟨93488302376089795608868565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62325534917393197072579043 93488302376089795608868565)
          ·
            refine ⟨2191132086939604584582857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 93488302376089795608868565 2191132086939604584582857)
            ·
              refine ⟨1643349065204703438437143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191132086939604584582857 1643349065204703438437143)
              ·
                refine ⟨2465023597807055157655715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643349065204703438437143 2465023597807055157655715)
                ·
                  refine ⟨3697535396710582736483573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465023597807055157655715 3697535396710582736483573)
                  ·
                    refine ⟨346643943441617131545335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3697535396710582736483573 346643943441617131545335)
                    ·
                      rfl

theorem cell23_2025260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_2025260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025260 prefixEnd_2025260 := by exact prefixLift 2025260
  have htrace : WordTrace (prefixWord ++ tailWord_2025260) baseStart_2025260 baseEnd_2025260 := by
    simpa [prefixWord, tailWord_2025260, baseEnd_2025260] using wordTrace_append hprefix tailTrace_2025260
  have hstable : (prefixWord ++ tailWord_2025260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025260).length < 2 ^ (prefixWord ++ tailWord_2025260).sum := by decide
  have hdescent : baseEnd_2025260 < baseStart_2025260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025276 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_2025276 : Nat := 118140960795 + 2025276 * 2 ^ 59
def prefixEnd_2025276 : Nat := 4983230072969 + 3 ^ 40 * 2025276 * 2
def baseEnd_2025276 : Nat := 1039940046015323332035931

theorem tailTrace_2025276 : CollatzResearch.WordTrace tailWord_2025276 prefixEnd_2025276 1039940046015323332035931 := by
  unfold tailWord_2025276
  simp only [CollatzResearch.WordTrace]
  refine ⟨36933942105389208224115841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49245256140518944298821121 36933942105389208224115841)
  ·
    refine ⟨27700456579041906168086881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36933942105389208224115841 27700456579041906168086881)
    ·
      refine ⟨20775342434281429626065161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27700456579041906168086881 20775342434281429626065161)
      ·
        refine ⟨15581506825711072219548871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20775342434281429626065161 15581506825711072219548871)
        ·
          refine ⟨23372260238566608329323307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581506825711072219548871 23372260238566608329323307)
          ·
            refine ⟨35058390357849912493984961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372260238566608329323307 35058390357849912493984961)
            ·
              refine ⟨26293792768387434370488721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35058390357849912493984961 26293792768387434370488721)
              ·
                refine ⟨19720344576290575777866541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26293792768387434370488721 19720344576290575777866541)
                ·
                  refine ⟨7395129216108965916699953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19720344576290575777866541 7395129216108965916699953)
                  ·
                    refine ⟨5546346912081724437524965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7395129216108965916699953 5546346912081724437524965)
                    ·
                      refine ⟨1039940046015323332035931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5546346912081724437524965 1039940046015323332035931)
                      ·
                        rfl

theorem cell23_2025276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_2025276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025276 prefixEnd_2025276 := by exact prefixLift 2025276
  have htrace : WordTrace (prefixWord ++ tailWord_2025276) baseStart_2025276 baseEnd_2025276 := by
    simpa [prefixWord, tailWord_2025276, baseEnd_2025276] using wordTrace_append hprefix tailTrace_2025276
  have hstable : (prefixWord ++ tailWord_2025276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025276).length < 2 ^ (prefixWord ++ tailWord_2025276).sum := by decide
  have hdescent : baseEnd_2025276 < baseStart_2025276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025290 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 2, 4]
def baseStart_2025290 : Nat := 118140960795 + 2025290 * 2 ^ 59
def prefixEnd_2025290 : Nat := 4983230072969 + 3 ^ 40 * 2025290 * 2
def baseEnd_2025290 : Nat := 346649078248162092420289

theorem tailTrace_2025290 : CollatzResearch.WordTrace tailWord_2025290 prefixEnd_2025290 346649078248162092420289 := by
  unfold tailWord_2025290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18467098708181924209810331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49245596555151797892827549 18467098708181924209810331)
  ·
    refine ⟨27700648062272886314715497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18467098708181924209810331 27700648062272886314715497)
    ·
      refine ⟨20775486046704664736036623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27700648062272886314715497 20775486046704664736036623)
      ·
        refine ⟨31163229070056997104054935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20775486046704664736036623 31163229070056997104054935)
        ·
          refine ⟨46744843605085495656082403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31163229070056997104054935 46744843605085495656082403)
          ·
            refine ⟨70117265407628243484123605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46744843605085495656082403 70117265407628243484123605)
            ·
              refine ⟨1643373407991286956659147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 70117265407628243484123605 1643373407991286956659147)
              ·
                refine ⟨2465060111986930434988721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643373407991286956659147 2465060111986930434988721)
                ·
                  refine ⟨1848795083990197826241541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465060111986930434988721 1848795083990197826241541)
                  ·
                    refine ⟨346649078248162092420289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1848795083990197826241541 346649078248162092420289)
                    ·
                      rfl

theorem cell23_2025290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_2025290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025290 prefixEnd_2025290 := by exact prefixLift 2025290
  have htrace : WordTrace (prefixWord ++ tailWord_2025290) baseStart_2025290 baseEnd_2025290 := by
    simpa [prefixWord, tailWord_2025290, baseEnd_2025290] using wordTrace_append hprefix tailTrace_2025290
  have hstable : (prefixWord ++ tailWord_2025290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025290).length < 2 ^ (prefixWord ++ tailWord_2025290).sum := by decide
  have hdescent : baseEnd_2025290 < baseStart_2025290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025300 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2025300 : Nat := 118140960795 + 2025300 * 2 ^ 59
def prefixEnd_2025300 : Nat := 4983230072969 + 3 ^ 40 * 2025300 * 2
def baseEnd_2025300 : Nat := 1039952369551031238135821

theorem tailTrace_2025300 : CollatzResearch.WordTrace tailWord_2025300 prefixEnd_2025300 1039952369551031238135821 := by
  unfold tailWord_2025300
  simp only [CollatzResearch.WordTrace]
  refine ⟨36934379781345734273552677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49245839708460979031403569 36934379781345734273552677)
  ·
    refine ⟨6925196209002325176291127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36934379781345734273552677 6925196209002325176291127)
    ·
      refine ⟨10387794313503487764436691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6925196209002325176291127 10387794313503487764436691)
      ·
        refine ⟨15581691470255231646655037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10387794313503487764436691 15581691470255231646655037)
        ·
          refine ⟨5843134301345711867495639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15581691470255231646655037 5843134301345711867495639)
          ·
            refine ⟨8764701452018567801243459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843134301345711867495639 8764701452018567801243459)
            ·
              refine ⟨13147052178027851701865189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764701452018567801243459 13147052178027851701865189)
              ·
                refine ⟨2465072283380222194099723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13147052178027851701865189 2465072283380222194099723)
                ·
                  refine ⟨3697608425070333291149585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465072283380222194099723 3697608425070333291149585)
                  ·
                    refine ⟨2773206318802749968362189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697608425070333291149585 2773206318802749968362189)
                    ·
                      refine ⟨1039952369551031238135821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2773206318802749968362189 1039952369551031238135821)
                      ·
                        rfl

theorem cell23_2025300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2025300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025300 prefixEnd_2025300 := by exact prefixLift 2025300
  have htrace : WordTrace (prefixWord ++ tailWord_2025300) baseStart_2025300 baseEnd_2025300 := by
    simpa [prefixWord, tailWord_2025300, baseEnd_2025300] using wordTrace_append hprefix tailTrace_2025300
  have hstable : (prefixWord ++ tailWord_2025300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025300).length < 2 ^ (prefixWord ++ tailWord_2025300).sum := by decide
  have hdescent : baseEnd_2025300 < baseStart_2025300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025313 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_2025313 : Nat := 118140960795 + 2025313 * 2 ^ 59
def prefixEnd_2025313 : Nat := 4983230072969 + 3 ^ 40 * 2025313 * 2
def baseEnd_2025313 : Nat := 1039959044799539687273261

theorem tailTrace_2025313 : CollatzResearch.WordTrace tailWord_2025313 prefixEnd_2025313 1039959044799539687273261 := by
  unfold tailWord_2025313
  simp only [CollatzResearch.WordTrace]
  refine ⟨73869233711644371767328593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49246155807762914511552395 73869233711644371767328593)
  ·
    refine ⟨55401925283733278825496445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73869233711644371767328593 55401925283733278825496445)
    ·
      refine ⟨20775721981399979559561167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55401925283733278825496445 20775721981399979559561167)
      ·
        refine ⟨31163582972099969339341751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20775721981399979559561167 31163582972099969339341751)
        ·
          refine ⟨46745374458149954009012627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31163582972099969339341751 46745374458149954009012627)
          ·
            refine ⟨70118061687224931013518941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46745374458149954009012627 70118061687224931013518941)
            ·
              refine ⟨26294273132709349130069603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70118061687224931013518941 26294273132709349130069603)
              ·
                refine ⟨39441409699064023695104405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26294273132709349130069603 39441409699064023695104405)
                ·
                  refine ⟨1848816079643626110708019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39441409699064023695104405 1848816079643626110708019)
                  ·
                    refine ⟨2773224119465439166062029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848816079643626110708019 2773224119465439166062029)
                    ·
                      refine ⟨1039959044799539687273261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2773224119465439166062029 1039959044799539687273261)
                      ·
                        rfl

theorem cell23_2025313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_2025313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025313 prefixEnd_2025313 := by exact prefixLift 2025313
  have htrace : WordTrace (prefixWord ++ tailWord_2025313) baseStart_2025313 baseEnd_2025313 := by
    simpa [prefixWord, tailWord_2025313, baseEnd_2025313] using wordTrace_append hprefix tailTrace_2025313
  have hstable : (prefixWord ++ tailWord_2025313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025313).length < 2 ^ (prefixWord ++ tailWord_2025313).sum := by decide
  have hdescent : baseEnd_2025313 < baseStart_2025313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025323 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 5, 3, 2]
def baseStart_2025323 : Nat := 118140960795 + 2025323 * 2 ^ 59
def prefixEnd_2025323 : Nat := 4983230072969 + 3 ^ 40 * 2025323 * 2
def baseEnd_2025323 : Nat := 1039964179606084648148215

theorem tailTrace_2025323 : CollatzResearch.WordTrace tailWord_2025323 prefixEnd_2025323 1039964179606084648148215 := by
  unfold tailWord_2025323
  simp only [CollatzResearch.WordTrace]
  refine ⟨73869598441608143475192623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49246398961072095650128415 73869598441608143475192623)
  ·
    refine ⟨110804397662412215212788935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73869598441608143475192623 110804397662412215212788935)
    ·
      refine ⟨166206596493618322819183403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110804397662412215212788935 166206596493618322819183403)
      ·
        refine ⟨249309894740427484228775105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166206596493618322819183403 249309894740427484228775105)
        ·
          refine ⟨186982421055320613171581329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249309894740427484228775105 186982421055320613171581329)
          ·
            refine ⟨140236815791490459878685997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186982421055320613171581329 140236815791490459878685997)
            ·
              refine ⟨52588805921808922454507249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140236815791490459878685997 52588805921808922454507249)
              ·
                refine ⟨39441604441356691840880437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52588805921808922454507249 39441604441356691840880437)
                ·
                  refine ⟨3697650416377189860082541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39441604441356691840880437 3697650416377189860082541)
                  ·
                    refine ⟨1386618906141446197530953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3697650416377189860082541 1386618906141446197530953)
                    ·
                      refine ⟨1039964179606084648148215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386618906141446197530953 1039964179606084648148215)
                      ·
                        rfl

theorem cell23_2025323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3, 2].length) (baseStart_2025323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025323 prefixEnd_2025323 := by exact prefixLift 2025323
  have htrace : WordTrace (prefixWord ++ tailWord_2025323) baseStart_2025323 baseEnd_2025323 := by
    simpa [prefixWord, tailWord_2025323, baseEnd_2025323] using wordTrace_append hprefix tailTrace_2025323
  have hstable : (prefixWord ++ tailWord_2025323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025323).length < 2 ^ (prefixWord ++ tailWord_2025323).sum := by decide
  have hdescent : baseEnd_2025323 < baseStart_2025323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025330 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2025330 : Nat := 118140960795 + 2025330 * 2 ^ 59
def prefixEnd_2025330 : Nat := 4983230072969 + 3 ^ 40 * 2025330 * 2
def baseEnd_2025330 : Nat := 1039967773970666120760683

theorem tailTrace_2025330 : CollatzResearch.WordTrace tailWord_2025330 prefixEnd_2025330 1039967773970666120760683 := by
  unfold tailWord_2025330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18467463438145695917674361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49246569168388522447131629 18467463438145695917674361)
  ·
    refine ⟨13850597578609271938255771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18467463438145695917674361 13850597578609271938255771)
    ·
      refine ⟨20775896367913907907383657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13850597578609271938255771 20775896367913907907383657)
      ·
        refine ⟨15581922275935430930537743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20775896367913907907383657 15581922275935430930537743)
        ·
          refine ⟨23372883413903146395806615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15581922275935430930537743 23372883413903146395806615)
          ·
            refine ⟨35059325120854719593709923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23372883413903146395806615 35059325120854719593709923)
            ·
              refine ⟨52588987681282079390564885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35059325120854719593709923 52588987681282079390564885)
              ·
                refine ⟨2465108797560097471432729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52588987681282079390564885 2465108797560097471432729)
                ·
                  refine ⟨1848831598170073103574547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465108797560097471432729 1848831598170073103574547)
                  ·
                    refine ⟨2773247397255109655361821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848831598170073103574547 2773247397255109655361821)
                    ·
                      refine ⟨1039967773970666120760683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2773247397255109655361821 1039967773970666120760683)
                      ·
                        rfl

theorem cell23_2025330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2025330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025330 prefixEnd_2025330 := by exact prefixLift 2025330
  have htrace : WordTrace (prefixWord ++ tailWord_2025330) baseStart_2025330 baseEnd_2025330 := by
    simpa [prefixWord, tailWord_2025330, baseEnd_2025330] using wordTrace_append hprefix tailTrace_2025330
  have hstable : (prefixWord ++ tailWord_2025330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025330).length < 2 ^ (prefixWord ++ tailWord_2025330).sum := by decide
  have hdescent : baseEnd_2025330 < baseStart_2025330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025347 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 2, 1, 3]
def baseStart_2025347 : Nat := 118140960795 + 2025347 * 2 ^ 59
def prefixEnd_2025347 : Nat := 4983230072969 + 3 ^ 40 * 2025347 * 2
def baseEnd_2025347 : Nat := 1039976503141792554248105

theorem tailTrace_2025347 : CollatzResearch.WordTrace tailWord_2025347 prefixEnd_2025347 1039976503141792554248105 := by
  unfold tailWord_2025347
  simp only [CollatzResearch.WordTrace]
  refine ⟨73870473793521195574066295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49246982529014130382710863 73870473793521195574066295)
  ·
    refine ⟨110805710690281793361099443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73870473793521195574066295 110805710690281793361099443)
    ·
      refine ⟨166208566035422690041649165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110805710690281793361099443 166208566035422690041649165)
      ·
        refine ⟨62328212263283508765618437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166208566035422690041649165 62328212263283508765618437)
        ·
          refine ⟨11686539799365657893553457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62328212263283508765618437 11686539799365657893553457)
          ·
            refine ⟨8764904849524243420165093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11686539799365657893553457 8764904849524243420165093)
            ·
              refine ⟨1643419659285795641280955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8764904849524243420165093 1643419659285795641280955)
              ·
                refine ⟨2465129488928693461921433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643419659285795641280955 2465129488928693461921433)
                ·
                  refine ⟨1848847116696520096441075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465129488928693461921433 1848847116696520096441075)
                  ·
                    refine ⟨2773270675044780144661613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1848847116696520096441075 2773270675044780144661613)
                    ·
                      refine ⟨1039976503141792554248105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2773270675044780144661613 1039976503141792554248105)
                      ·
                        rfl

theorem cell23_2025347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_2025347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025347 prefixEnd_2025347 := by exact prefixLift 2025347
  have htrace : WordTrace (prefixWord ++ tailWord_2025347) baseStart_2025347 baseEnd_2025347 := by
    simpa [prefixWord, tailWord_2025347, baseEnd_2025347] using wordTrace_append hprefix tailTrace_2025347
  have hstable : (prefixWord ++ tailWord_2025347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025347).length < 2 ^ (prefixWord ++ tailWord_2025347).sum := by decide
  have hdescent : baseEnd_2025347 < baseStart_2025347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025370 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2]
def baseStart_2025370 : Nat := 118140960795 + 2025370 * 2 ^ 59
def prefixEnd_2025370 : Nat := 4983230072969 + 3 ^ 40 * 2025370 * 2
def baseEnd_2025370 : Nat := 1039988313196845964260499

theorem tailTrace_2025370 : CollatzResearch.WordTrace tailWord_2025370 prefixEnd_2025370 1039988313196845964260499 := by
  unfold tailWord_2025370
  simp only [CollatzResearch.WordTrace]
  refine ⟨18467828168109467625538391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49247541781625247001435709 18467828168109467625538391)
  ·
    refine ⟨27701742252164201438307587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18467828168109467625538391 27701742252164201438307587)
    ·
      refine ⟨41552613378246302157461381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27701742252164201438307587 41552613378246302157461381)
      ·
        refine ⟨7791115008421181654524009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41552613378246302157461381 7791115008421181654524009)
        ·
          refine ⟨5843336256315886240893007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7791115008421181654524009 5843336256315886240893007)
          ·
            refine ⟨8765004384473829361339511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843336256315886240893007 8765004384473829361339511)
            ·
              refine ⟨13147506576710744042009267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765004384473829361339511 13147506576710744042009267)
              ·
                refine ⟨19721259865066116063013901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13147506576710744042009267 19721259865066116063013901)
                ·
                  refine ⟨7395472449399793523630213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19721259865066116063013901 7395472449399793523630213)
                  ·
                    refine ⟨1386651084262461285680665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7395472449399793523630213 1386651084262461285680665)
                    ·
                      refine ⟨1039988313196845964260499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386651084262461285680665 1039988313196845964260499)
                      ·
                        rfl

theorem cell23_2025370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_2025370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025370 prefixEnd_2025370 := by exact prefixLift 2025370
  have htrace : WordTrace (prefixWord ++ tailWord_2025370) baseStart_2025370 baseEnd_2025370 := by
    simpa [prefixWord, tailWord_2025370, baseEnd_2025370] using wordTrace_append hprefix tailTrace_2025370
  have hstable : (prefixWord ++ tailWord_2025370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025370).length < 2 ^ (prefixWord ++ tailWord_2025370).sum := by decide
  have hdescent : baseEnd_2025370 < baseStart_2025370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025373 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2025373 : Nat := 118140960795 + 2025373 * 2 ^ 59
def prefixEnd_2025373 : Nat := 4983230072969 + 3 ^ 40 * 2025373 * 2
def baseEnd_2025373 : Nat := 1039989853638809452522985

theorem tailTrace_2025373 : CollatzResearch.WordTrace tailWord_2025373 prefixEnd_2025373 1039989853638809452522985 := by
  unfold tailWord_2025373
  simp only [CollatzResearch.WordTrace]
  refine ⟨73871422091427002014512773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49247614727618001343008515 73871422091427002014512773)
  ·
    refine ⟨13850891642142562877721145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73871422091427002014512773 13850891642142562877721145)
    ·
      refine ⟨10388168731606922158290859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13850891642142562877721145 10388168731606922158290859)
      ·
        refine ⟨15582253097410383237436289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10388168731606922158290859 15582253097410383237436289)
        ·
          refine ⟨11686689823057787428077217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15582253097410383237436289 11686689823057787428077217)
          ·
            refine ⟨8765017367293340571057913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11686689823057787428077217 8765017367293340571057913)
            ·
              refine ⟨6573763025470005428293435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765017367293340571057913 6573763025470005428293435)
              ·
                refine ⟨9860644538205008142440153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6573763025470005428293435 9860644538205008142440153)
                ·
                  refine ⟨7395483403653756106830115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9860644538205008142440153 7395483403653756106830115)
                  ·
                    refine ⟨11093225105480634160245173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395483403653756106830115 11093225105480634160245173)
                    ·
                      refine ⟨1039989853638809452522985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11093225105480634160245173 1039989853638809452522985)
                      ·
                        rfl

theorem cell23_2025373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2025373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025373 prefixEnd_2025373 := by exact prefixLift 2025373
  have htrace : WordTrace (prefixWord ++ tailWord_2025373) baseStart_2025373 baseEnd_2025373 := by
    simpa [prefixWord, tailWord_2025373, baseEnd_2025373] using wordTrace_append hprefix tailTrace_2025373
  have hstable : (prefixWord ++ tailWord_2025373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025373).length < 2 ^ (prefixWord ++ tailWord_2025373).sum := by decide
  have hdescent : baseEnd_2025373 < baseStart_2025373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025404 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2025404 : Nat := 118140960795 + 2025404 * 2 ^ 59
def prefixEnd_2025404 : Nat := 4983230072969 + 3 ^ 40 * 2025404 * 2
def baseEnd_2025404 : Nat := 1040005771539098831235343

theorem tailTrace_2025404 : CollatzResearch.WordTrace tailWord_2025404 prefixEnd_2025404 1040005771539098831235343 := by
  unfold tailWord_2025404
  simp only [CollatzResearch.WordTrace]
  refine ⟨36936276377157347154445633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49248368502876462872594177 36936276377157347154445633)
  ·
    refine ⟨27702207282868010365834225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36936276377157347154445633 27702207282868010365834225)
    ·
      refine ⟨20776655462151007774375669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27702207282868010365834225 20776655462151007774375669)
      ·
        refine ⟨1947811449576656978847719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20776655462151007774375669 1947811449576656978847719)
        ·
          refine ⟨2921717174364985468271579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947811449576656978847719 2921717174364985468271579)
          ·
            refine ⟨4382575761547478202407369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921717174364985468271579 4382575761547478202407369)
            ·
              refine ⟨3286931821160608651805527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4382575761547478202407369 3286931821160608651805527)
              ·
                refine ⟨4930397731740912977708291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3286931821160608651805527 4930397731740912977708291)
                ·
                  refine ⟨7395596597611369466562437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930397731740912977708291 7395596597611369466562437)
                  ·
                    refine ⟨1386674362052131774980457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7395596597611369466562437 1386674362052131774980457)
                    ·
                      refine ⟨1040005771539098831235343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386674362052131774980457 1040005771539098831235343)
                      ·
                        rfl

theorem cell23_2025404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2025404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025404 prefixEnd_2025404 := by exact prefixLift 2025404
  have htrace : WordTrace (prefixWord ++ tailWord_2025404) baseStart_2025404 baseEnd_2025404 := by
    simpa [prefixWord, tailWord_2025404, baseEnd_2025404] using wordTrace_append hprefix tailTrace_2025404
  have hstable : (prefixWord ++ tailWord_2025404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025404).length < 2 ^ (prefixWord ++ tailWord_2025404).sum := by decide
  have hdescent : baseEnd_2025404 < baseStart_2025404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025473 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2025473 : Nat := 118140960795 + 2025473 * 2 ^ 59
def prefixEnd_2025473 : Nat := 4983230072969 + 3 ^ 40 * 2025473 * 2
def baseEnd_2025473 : Nat := 1040041201704259061272525

theorem tailTrace_2025473 : CollatzResearch.WordTrace tailWord_2025473 prefixEnd_2025473 1040041201704259061272525 := by
  unfold tailWord_2025473
  simp only [CollatzResearch.WordTrace]
  refine ⟨73875069391064719093153073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49250046260709812728768715 73875069391064719093153073)
  ·
    refine ⟨55406302043298539319864805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73875069391064719093153073 55406302043298539319864805)
    ·
      refine ⟨10388681633118476122474651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55406302043298539319864805 10388681633118476122474651)
      ·
        refine ⟨15583022449677714183711977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10388681633118476122474651 15583022449677714183711977)
        ·
          refine ⟨11687266837258285637783983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15583022449677714183711977 11687266837258285637783983)
          ·
            refine ⟨17530900255887428456675975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687266837258285637783983 17530900255887428456675975)
            ·
              refine ⟨26296350383831142685013963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17530900255887428456675975 26296350383831142685013963)
              ·
                refine ⟨39444525575746714027520945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26296350383831142685013963 39444525575746714027520945)
                ·
                  refine ⟨29583394181810035520640709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39444525575746714027520945 29583394181810035520640709)
                  ·
                    refine ⟨5546886409089381660120133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29583394181810035520640709 5546886409089381660120133)
                    ·
                      refine ⟨1040041201704259061272525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5546886409089381660120133 1040041201704259061272525)
                      ·
                        rfl

theorem cell23_2025473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2025473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025473 prefixEnd_2025473 := by exact prefixLift 2025473
  have htrace : WordTrace (prefixWord ++ tailWord_2025473) baseStart_2025473 baseEnd_2025473 := by
    simpa [prefixWord, tailWord_2025473, baseEnd_2025473] using wordTrace_append hprefix tailTrace_2025473
  have hstable : (prefixWord ++ tailWord_2025473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025473).length < 2 ^ (prefixWord ++ tailWord_2025473).sum := by decide
  have hdescent : baseEnd_2025473 < baseStart_2025473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025480 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_2025480 : Nat := 118140960795 + 2025480 * 2 ^ 59
def prefixEnd_2025480 : Nat := 4983230072969 + 3 ^ 40 * 2025480 * 2
def baseEnd_2025480 : Nat := 1040044796068840533884993

theorem tailTrace_2025480 : CollatzResearch.WordTrace tailWord_2025480 prefixEnd_2025480 1040044796068840533884993 := by
  unfold tailWord_2025480
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937662351019679644328947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49250216468026239525771929 36937662351019679644328947)
  ·
    refine ⟨55406493526529519466493421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36937662351019679644328947 55406493526529519466493421)
    ·
      refine ⟨20777435072448569799935033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55406493526529519466493421 20777435072448569799935033)
      ·
        refine ⟨15583076304336427349951275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20777435072448569799935033 15583076304336427349951275)
        ·
          refine ⟨23374614456504641024926913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15583076304336427349951275 23374614456504641024926913)
          ·
            refine ⟨17530960842378480768695185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23374614456504641024926913 17530960842378480768695185)
            ·
              refine ⟨13148220631783860576521389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17530960842378480768695185 13148220631783860576521389)
              ·
                refine ⟨4930582736918947716195521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13148220631783860576521389 4930582736918947716195521)
                ·
                  refine ⟨3697937052689210787146641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4930582736918947716195521 3697937052689210787146641)
                  ·
                    refine ⟨2773452789516908090359981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3697937052689210787146641 2773452789516908090359981)
                    ·
                      refine ⟨1040044796068840533884993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2773452789516908090359981 1040044796068840533884993)
                      ·
                        rfl

theorem cell23_2025480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_2025480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025480 prefixEnd_2025480 := by exact prefixLift 2025480
  have htrace : WordTrace (prefixWord ++ tailWord_2025480) baseStart_2025480 baseEnd_2025480 := by
    simpa [prefixWord, tailWord_2025480, baseEnd_2025480] using wordTrace_append hprefix tailTrace_2025480
  have hstable : (prefixWord ++ tailWord_2025480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025480).length < 2 ^ (prefixWord ++ tailWord_2025480).sum := by decide
  have hdescent : baseEnd_2025480 < baseStart_2025480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025580 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_2025580 : Nat := 118140960795 + 2025580 * 2 ^ 59
def prefixEnd_2025580 : Nat := 4983230072969 + 3 ^ 40 * 2025580 * 2
def baseEnd_2025580 : Nat := 1040096144134290142634533

theorem tailTrace_2025580 : CollatzResearch.WordTrace tailWord_2025580 prefixEnd_2025580 1040096144134290142634533 := by
  unfold tailWord_2025580
  simp only [CollatzResearch.WordTrace]
  refine ⟨36939486000838538183649097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49252648001118050911532129 36939486000838538183649097)
  ·
    refine ⟨27704614500628903637736823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36939486000838538183649097 27704614500628903637736823)
    ·
      refine ⟨41556921750943355456605235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27704614500628903637736823 41556921750943355456605235)
      ·
        refine ⟨62335382626415033184907853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41556921750943355456605235 62335382626415033184907853)
        ·
          refine ⟨23375768484905637444340445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62335382626415033184907853 23375768484905637444340445)
          ·
            refine ⟨8765913181839614041627667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23375768484905637444340445 8765913181839614041627667)
            ·
              refine ⟨13148869772759421062441501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765913181839614041627667 13148869772759421062441501)
              ·
                refine ⟨4930826164784782898415563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13148869772759421062441501 4930826164784782898415563)
                ·
                  refine ⟨7396239247177174347623345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930826164784782898415563 7396239247177174347623345)
                  ·
                    refine ⟨5547179435382880760717509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7396239247177174347623345 5547179435382880760717509)
                    ·
                      refine ⟨1040096144134290142634533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5547179435382880760717509 1040096144134290142634533)
                      ·
                        rfl

theorem cell23_2025580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_2025580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025580 prefixEnd_2025580 := by exact prefixLift 2025580
  have htrace : WordTrace (prefixWord ++ tailWord_2025580) baseStart_2025580 baseEnd_2025580 := by
    simpa [prefixWord, tailWord_2025580, baseEnd_2025580] using wordTrace_append hprefix tailTrace_2025580
  have hstable : (prefixWord ++ tailWord_2025580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025580).length < 2 ^ (prefixWord ++ tailWord_2025580).sum := by decide
  have hdescent : baseEnd_2025580 < baseStart_2025580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025584 : List Nat := [2, 1, 1, 1, 5, 3, 1, 2, 3, 2, 2]
def baseStart_2025584 : Nat := 118140960795 + 2025584 * 2 ^ 59
def prefixEnd_2025584 : Nat := 4983230072969 + 3 ^ 40 * 2025584 * 2
def baseEnd_2025584 : Nat := 1040098198056908126984515

theorem tailTrace_2025584 : CollatzResearch.WordTrace tailWord_2025584 prefixEnd_2025584 1040098198056908126984515 := by
  unfold tailWord_2025584
  simp only [CollatzResearch.WordTrace]
  refine ⟨36939558946831292525221903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49252745262441723366962537 36939558946831292525221903)
  ·
    refine ⟨55409338420246938787832855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36939558946831292525221903 55409338420246938787832855)
    ·
      refine ⟨83114007630370408181749283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55409338420246938787832855 83114007630370408181749283)
      ·
        refine ⟨124671011445555612272623925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83114007630370408181749283 124671011445555612272623925)
        ·
          refine ⟨11687907323020838650558493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124671011445555612272623925 11687907323020838650558493)
          ·
            refine ⟨4382965246132814493959435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11687907323020838650558493 4382965246132814493959435)
            ·
              refine ⟨6574447869199221740939153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4382965246132814493959435 6574447869199221740939153)
              ·
                refine ⟨4930835901899416305704365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6574447869199221740939153 4930835901899416305704365)
                ·
                  refine ⟨1849063463212281114639137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4930835901899416305704365 1849063463212281114639137)
                  ·
                    refine ⟨1386797597409210835979353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1849063463212281114639137 1386797597409210835979353)
                    ·
                      refine ⟨1040098198056908126984515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386797597409210835979353 1040098198056908126984515)
                      ·
                        rfl

theorem cell23_2025584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 2, 3, 2, 2].length) (baseStart_2025584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025584 prefixEnd_2025584 := by exact prefixLift 2025584
  have htrace : WordTrace (prefixWord ++ tailWord_2025584) baseStart_2025584 baseEnd_2025584 := by
    simpa [prefixWord, tailWord_2025584, baseEnd_2025584] using wordTrace_append hprefix tailTrace_2025584
  have hstable : (prefixWord ++ tailWord_2025584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025584).length < 2 ^ (prefixWord ++ tailWord_2025584).sum := by decide
  have hdescent : baseEnd_2025584 < baseStart_2025584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025601 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_2025601 : Nat := 118140960795 + 2025601 * 2 ^ 59
def prefixEnd_2025601 : Nat := 4983230072969 + 3 ^ 40 * 2025601 * 2
def baseEnd_2025601 : Nat := 1040106927228034560471937

theorem tailTrace_2025601 : CollatzResearch.WordTrace tailWord_2025601 prefixEnd_2025601 1040106927228034560471937 := by
  unfold tailWord_2025601
  simp only [CollatzResearch.WordTrace]
  refine ⟨73879737934600996953812657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49253158623067331302541771 73879737934600996953812657)
  ·
    refine ⟨55409803450950747715359493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73879737934600996953812657 55409803450950747715359493)
    ·
      refine ⟨10389338147053265196629905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55409803450950747715359493 10389338147053265196629905)
      ·
        refine ⟨7792003610289948897472429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10389338147053265196629905 7792003610289948897472429)
        ·
          refine ⟨2922001353858730836552161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7792003610289948897472429 2922001353858730836552161)
          ·
            refine ⟨2191501015394048127414121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922001353858730836552161 2191501015394048127414121)
            ·
              refine ⟨1643625761545536095560591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191501015394048127414121 1643625761545536095560591)
              ·
                refine ⟨2465438642318304143340887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643625761545536095560591 2465438642318304143340887)
                ·
                  refine ⟨3698157963477456215011331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465438642318304143340887 3698157963477456215011331)
                  ·
                    refine ⟨5547236945216184322516997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698157963477456215011331 5547236945216184322516997)
                    ·
                      refine ⟨1040106927228034560471937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5547236945216184322516997 1040106927228034560471937)
                      ·
                        rfl

theorem cell23_2025601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_2025601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025601 prefixEnd_2025601 := by exact prefixLift 2025601
  have htrace : WordTrace (prefixWord ++ tailWord_2025601) baseStart_2025601 baseEnd_2025601 := by
    simpa [prefixWord, tailWord_2025601, baseEnd_2025601] using wordTrace_append hprefix tailTrace_2025601
  have hstable : (prefixWord ++ tailWord_2025601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025601).length < 2 ^ (prefixWord ++ tailWord_2025601).sum := by decide
  have hdescent : baseEnd_2025601 < baseStart_2025601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025634 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2025634 : Nat := 118140960795 + 2025634 * 2 ^ 59
def prefixEnd_2025634 : Nat := 4983230072969 + 3 ^ 40 * 2025634 * 2
def baseEnd_2025634 : Nat := 1040123872089632931359285

theorem tailTrace_2025634 : CollatzResearch.WordTrace tailWord_2025634 prefixEnd_2025634 1040123872089632931359285 := by
  unfold tailWord_2025634
  simp only [CollatzResearch.WordTrace]
  refine ⟨18470235385870360897440989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49253961028987629059842637 18470235385870360897440989)
  ·
    refine ⟨6926338269701385336540371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18470235385870360897440989 6926338269701385336540371)
    ·
      refine ⟨10389507404552078004810557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6926338269701385336540371 10389507404552078004810557)
      ·
        refine ⟨3896065276707029251803959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10389507404552078004810557 3896065276707029251803959)
        ·
          refine ⟨5844097915060543877705939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896065276707029251803959 5844097915060543877705939)
          ·
            refine ⟨8766146872590815816558909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5844097915060543877705939 8766146872590815816558909)
            ·
              refine ⟨3287305077221555931209591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8766146872590815816558909 3287305077221555931209591)
              ·
                refine ⟨4930957615832333896814387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287305077221555931209591 4930957615832333896814387)
                ·
                  refine ⟨7396436423748500845221581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930957615832333896814387 7396436423748500845221581)
                  ·
                    refine ⟨2773663658905687816958093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7396436423748500845221581 2773663658905687816958093)
                    ·
                      refine ⟨1040123872089632931359285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2773663658905687816958093 1040123872089632931359285)
                      ·
                        rfl

theorem cell23_2025634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2025634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025634 prefixEnd_2025634 := by exact prefixLift 2025634
  have htrace : WordTrace (prefixWord ++ tailWord_2025634) baseStart_2025634 baseEnd_2025634 := by
    simpa [prefixWord, tailWord_2025634, baseEnd_2025634] using wordTrace_append hprefix tailTrace_2025634
  have hstable : (prefixWord ++ tailWord_2025634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025634).length < 2 ^ (prefixWord ++ tailWord_2025634).sum := by decide
  have hdescent : baseEnd_2025634 < baseStart_2025634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025657 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 3, 4, 2]
def baseStart_2025657 : Nat := 118140960795 + 2025657 * 2 ^ 59
def prefixEnd_2025657 : Nat := 4983230072969 + 3 ^ 40 * 2025657 * 2
def baseEnd_2025657 : Nat := 1040135682144686341371679

theorem tailTrace_2025657 : CollatzResearch.WordTrace tailWord_2025657 prefixEnd_2025657 1040135682144686341371679 := by
  unfold tailWord_2025657
  simp only [CollatzResearch.WordTrace]
  refine ⟨73881780422398118517851225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49254520281598745678567483 73881780422398118517851225)
  ·
    refine ⟨55411335316798588888388419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73881780422398118517851225 55411335316798588888388419)
    ·
      refine ⟨83117002975197883332582629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55411335316798588888388419 83117002975197883332582629)
      ·
        refine ⟨15584438057849603124859243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83117002975197883332582629 15584438057849603124859243)
        ·
          refine ⟨23376657086774404687288865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15584438057849603124859243 23376657086774404687288865)
          ·
            refine ⟨17532492815080803515466649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23376657086774404687288865 17532492815080803515466649)
            ·
              refine ⟨13149369611310602636599987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17532492815080803515466649 13149369611310602636599987)
              ·
                refine ⟨19724054416965903954899981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13149369611310602636599987 19724054416965903954899981)
                ·
                  refine ⟨7396520406362213983087493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19724054416965903954899981 7396520406362213983087493)
                  ·
                    refine ⟨1386847576192915121828905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396520406362213983087493 1386847576192915121828905)
                    ·
                      refine ⟨1040135682144686341371679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386847576192915121828905 1040135682144686341371679)
                      ·
                        rfl

theorem cell23_2025657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_2025657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025657 prefixEnd_2025657 := by exact prefixLift 2025657
  have htrace : WordTrace (prefixWord ++ tailWord_2025657) baseStart_2025657 baseEnd_2025657 := by
    simpa [prefixWord, tailWord_2025657, baseEnd_2025657] using wordTrace_append hprefix tailTrace_2025657
  have hstable : (prefixWord ++ tailWord_2025657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025657).length < 2 ^ (prefixWord ++ tailWord_2025657).sum := by decide
  have hdescent : baseEnd_2025657 < baseStart_2025657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025674 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_2025674 : Nat := 118140960795 + 2025674 * 2 ^ 59
def prefixEnd_2025674 : Nat := 4983230072969 + 3 ^ 40 * 2025674 * 2
def baseEnd_2025674 : Nat := 1040144411315812774859101

theorem tailTrace_2025674 : CollatzResearch.WordTrace tailWord_2025674 prefixEnd_2025674 1040144411315812774859101 := by
  unfold tailWord_2025674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18470600115834132605305019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49254933642224353614146717 18470600115834132605305019)
  ·
    refine ⟨27705900173751198907957529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18470600115834132605305019 27705900173751198907957529)
    ·
      refine ⟨20779425130313399180968147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27705900173751198907957529 20779425130313399180968147)
      ·
        refine ⟨31169137695470098771452221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20779425130313399180968147 31169137695470098771452221)
        ·
          refine ⟨11688426635801287039294583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31169137695470098771452221 11688426635801287039294583)
          ·
            refine ⟨17532639953701930558941875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11688426635801287039294583 17532639953701930558941875)
            ·
              refine ⟨26298959930552895838412813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17532639953701930558941875 26298959930552895838412813)
              ·
                refine ⟨9862109973957335939404805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26298959930552895838412813 9862109973957335939404805)
                ·
                  refine ⟨1849145620117000488638401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9862109973957335939404805 1849145620117000488638401)
                  ·
                    refine ⟨1386859215087750366478801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1849145620117000488638401 1386859215087750366478801)
                    ·
                      refine ⟨1040144411315812774859101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1386859215087750366478801 1040144411315812774859101)
                      ·
                        rfl

theorem cell23_2025674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_2025674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025674 prefixEnd_2025674 := by exact prefixLift 2025674
  have htrace : WordTrace (prefixWord ++ tailWord_2025674) baseStart_2025674 baseEnd_2025674 := by
    simpa [prefixWord, tailWord_2025674, baseEnd_2025674] using wordTrace_append hprefix tailTrace_2025674
  have hstable : (prefixWord ++ tailWord_2025674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025674).length < 2 ^ (prefixWord ++ tailWord_2025674).sum := by decide
  have hdescent : baseEnd_2025674 < baseStart_2025674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025685 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2025685 : Nat := 118140960795 + 2025685 * 2 ^ 59
def prefixEnd_2025685 : Nat := 4983230072969 + 3 ^ 40 * 2025685 * 2
def baseEnd_2025685 : Nat := 1040150059603012231821551

theorem tailTrace_2025685 : CollatzResearch.WordTrace tailWord_2025685 prefixEnd_2025685 1040150059603012231821551 := by
  unfold tailWord_2025685
  simp only [CollatzResearch.WordTrace]
  refine ⟨73882801666296679299870509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49255201110864452866580339 73882801666296679299870509)
  ·
    refine ⟨27706050624861254737451441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73882801666296679299870509 27706050624861254737451441)
    ·
      refine ⟨20779537968645941053088581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27706050624861254737451441 20779537968645941053088581)
      ·
        refine ⟨3896163369121113947454109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20779537968645941053088581 3896163369121113947454109)
        ·
          refine ⟨1461061263420417730295291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3896163369121113947454109 1461061263420417730295291)
          ·
            refine ⟨2191591895130626595442937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461061263420417730295291 2191591895130626595442937)
            ·
              refine ⟨1643693921347969946582203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191591895130626595442937 1643693921347969946582203)
              ·
                refine ⟨2465540882021954919873305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643693921347969946582203 2465540882021954919873305)
                ·
                  refine ⟨1849155661516466189904979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465540882021954919873305 1849155661516466189904979)
                  ·
                    refine ⟨2773733492274699284857469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1849155661516466189904979 2773733492274699284857469)
                    ·
                      refine ⟨1040150059603012231821551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2773733492274699284857469 1040150059603012231821551)
                      ·
                        rfl

theorem cell23_2025685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2025685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025685 prefixEnd_2025685 := by exact prefixLift 2025685
  have htrace : WordTrace (prefixWord ++ tailWord_2025685) baseStart_2025685 baseEnd_2025685 := by
    simpa [prefixWord, tailWord_2025685, baseEnd_2025685] using wordTrace_append hprefix tailTrace_2025685
  have hstable : (prefixWord ++ tailWord_2025685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025685).length < 2 ^ (prefixWord ++ tailWord_2025685).sum := by decide
  have hdescent : baseEnd_2025685 < baseStart_2025685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025764 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2025764 : Nat := 118140960795 + 2025764 * 2 ^ 59
def prefixEnd_2025764 : Nat := 4983230072969 + 3 ^ 40 * 2025764 * 2
def baseEnd_2025764 : Nat := 1040190624574717422733687

theorem tailTrace_2025764 : CollatzResearch.WordTrace tailWord_2025764 prefixEnd_2025764 1040190624574717422733687 := by
  unfold tailWord_2025764
  simp only [CollatzResearch.WordTrace]
  refine ⟨36942841516505237895998173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49257122022006983861330897 36942841516505237895998173)
  ·
    refine ⟨13853565568689464210999315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36942841516505237895998173 13853565568689464210999315)
    ·
      refine ⟨20780348353034196316498973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13853565568689464210999315 20780348353034196316498973)
      ·
        refine ⟨7792630632387823618687115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20780348353034196316498973 7792630632387823618687115)
        ·
          refine ⟨11688945948581735428030673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792630632387823618687115 11688945948581735428030673)
          ·
            refine ⟨8766709461436301571023005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11688945948581735428030673 8766709461436301571023005)
            ·
              refine ⟨3287516048038613089133627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8766709461436301571023005 3287516048038613089133627)
              ·
                refine ⟨4931274072057919633700441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3287516048038613089133627 4931274072057919633700441)
                ·
                  refine ⟨3698455554043439725275331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4931274072057919633700441 3698455554043439725275331)
                  ·
                    refine ⟨5547683331065159587912997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3698455554043439725275331 5547683331065159587912997)
                    ·
                      refine ⟨1040190624574717422733687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5547683331065159587912997 1040190624574717422733687)
                      ·
                        rfl

theorem cell23_2025764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2025764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025764 prefixEnd_2025764 := by exact prefixLift 2025764
  have htrace : WordTrace (prefixWord ++ tailWord_2025764) baseStart_2025764 baseEnd_2025764 := by
    simpa [prefixWord, tailWord_2025764, baseEnd_2025764] using wordTrace_append hprefix tailTrace_2025764
  have hstable : (prefixWord ++ tailWord_2025764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025764).length < 2 ^ (prefixWord ++ tailWord_2025764).sum := by decide
  have hdescent : baseEnd_2025764 < baseStart_2025764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025804 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 6]
def baseStart_2025804 : Nat := 118140960795 + 2025804 * 2 ^ 59
def prefixEnd_2025804 : Nat := 4983230072969 + 3 ^ 40 * 2025804 * 2
def baseEnd_2025804 : Nat := 115579018200099696248167

theorem tailTrace_2025804 : CollatzResearch.WordTrace tailWord_2025804 prefixEnd_2025804 115579018200099696248167 := by
  unfold tailWord_2025804
  simp only [CollatzResearch.WordTrace]
  refine ⟨36943570976432781311726233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49258094635243708415634977 36943570976432781311726233)
  ·
    refine ⟨27707678232324585983794675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36943570976432781311726233 27707678232324585983794675)
    ·
      refine ⟨41561517348486878975692013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27707678232324585983794675 41561517348486878975692013)
      ·
        refine ⟨15585569005682579615884505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41561517348486878975692013 15585569005682579615884505)
        ·
          refine ⟨11689176754261934711913379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15585569005682579615884505 11689176754261934711913379)
          ·
            refine ⟨17533765131392902067870069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689176754261934711913379 17533765131392902067870069)
            ·
              refine ⟨1643790481068084568862819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17533765131392902067870069 1643790481068084568862819)
              ·
                refine ⟨2465685721602126853294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643790481068084568862819 2465685721602126853294229)
                ·
                  refine ⟨115579018200099696248167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2465685721602126853294229 115579018200099696248167)
                  ·
                    rfl

theorem cell23_2025804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_2025804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025804 prefixEnd_2025804 := by exact prefixLift 2025804
  have htrace : WordTrace (prefixWord ++ tailWord_2025804) baseStart_2025804 baseEnd_2025804 := by
    simpa [prefixWord, tailWord_2025804, baseEnd_2025804] using wordTrace_append hprefix tailTrace_2025804
  have hstable : (prefixWord ++ tailWord_2025804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025804).length < 2 ^ (prefixWord ++ tailWord_2025804).sum := by decide
  have hdescent : baseEnd_2025804 < baseStart_2025804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025867 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6]
def baseStart_2025867 : Nat := 118140960795 + 2025867 * 2 ^ 59
def prefixEnd_2025867 : Nat := 4983230072969 + 3 ^ 40 * 2025867 * 2
def baseEnd_2025867 : Nat := 1040243513082130519745713

theorem tailTrace_2025867 : CollatzResearch.WordTrace tailWord_2025867 prefixEnd_2025867 1040243513082130519745713 := by
  unfold tailWord_2025867
  simp only [CollatzResearch.WordTrace]
  refine ⟨73889439751637324382995855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49259626501091549588663903 73889439751637324382995855)
  ·
    refine ⟨110834159627455986574493783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73889439751637324382995855 110834159627455986574493783)
    ·
      refine ⟨166251239441183979861740675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110834159627455986574493783 166251239441183979861740675)
      ·
        refine ⟨249376859161775969792611013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166251239441183979861740675 249376859161775969792611013)
        ·
          refine ⟨46758161092832994336114565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249376859161775969792611013 46758161092832994336114565)
          ·
            refine ⟨8767155204906186438021481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46758161092832994336114565 8767155204906186438021481)
            ·
              refine ⟨6575366403679639828516111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8767155204906186438021481 6575366403679639828516111)
              ·
                refine ⟨9863049605519459742774167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575366403679639828516111 9863049605519459742774167)
                ·
                  refine ⟨14794574408279189614161251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9863049605519459742774167 14794574408279189614161251)
                  ·
                    refine ⟨22191861612418784421241877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14794574408279189614161251 22191861612418784421241877)
                    ·
                      refine ⟨1040243513082130519745713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22191861612418784421241877 1040243513082130519745713)
                      ·
                        rfl

theorem cell23_2025867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_2025867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025867 prefixEnd_2025867 := by exact prefixLift 2025867
  have htrace : WordTrace (prefixWord ++ tailWord_2025867) baseStart_2025867 baseEnd_2025867 := by
    simpa [prefixWord, tailWord_2025867, baseEnd_2025867] using wordTrace_append hprefix tailTrace_2025867
  have hstable : (prefixWord ++ tailWord_2025867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025867).length < 2 ^ (prefixWord ++ tailWord_2025867).sum := by decide
  have hdescent : baseEnd_2025867 < baseStart_2025867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025904 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 8, 1, 3]
def baseStart_2025904 : Nat := 118140960795 + 2025904 * 2 ^ 59
def prefixEnd_2025904 : Nat := 4983230072969 + 3 ^ 40 * 2025904 * 2
def baseEnd_2025904 : Nat := 1040262511866346874983043

theorem tailTrace_2025904 : CollatzResearch.WordTrace tailWord_2025904 prefixEnd_2025904 1040262511866346874983043 := by
  unfold tailWord_2025904
  simp only [CollatzResearch.WordTrace]
  refine ⟨36945394626251639851046383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49260526168335519801395177 36945394626251639851046383)
  ·
    refine ⟨55418091939377459776569575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36945394626251639851046383 55418091939377459776569575)
    ·
      refine ⟨83127137909066189664854363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55418091939377459776569575 83127137909066189664854363)
      ·
        refine ⟨124690706863599284497281545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83127137909066189664854363 124690706863599284497281545)
        ·
          refine ⟨93518030147699463372961159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124690706863599284497281545 93518030147699463372961159)
          ·
            refine ⟨140277045221549195059441739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93518030147699463372961159 140277045221549195059441739)
            ·
              refine ⟨210415567832323792589162609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140277045221549195059441739 210415567832323792589162609)
              ·
                refine ⟨157811675874242844441871957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210415567832323792589162609 157811675874242844441871957)
                ·
                  refine ⟨1849355576651283333303187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 157811675874242844441871957 1849355576651283333303187)
                  ·
                    refine ⟨2774033364976924999954781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1849355576651283333303187 2774033364976924999954781)
                    ·
                      refine ⟨1040262511866346874983043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2774033364976924999954781 1040262511866346874983043)
                      ·
                        rfl

theorem cell23_2025904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 8, 1, 3].length) (baseStart_2025904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025904 prefixEnd_2025904 := by exact prefixLift 2025904
  have htrace : WordTrace (prefixWord ++ tailWord_2025904) baseStart_2025904 baseEnd_2025904 := by
    simpa [prefixWord, tailWord_2025904, baseEnd_2025904] using wordTrace_append hprefix tailTrace_2025904
  have hstable : (prefixWord ++ tailWord_2025904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025904).length < 2 ^ (prefixWord ++ tailWord_2025904).sum := by decide
  have hdescent : baseEnd_2025904 < baseStart_2025904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025905 : List Nat := [1, 2, 2, 4, 1, 3, 1, 4, 1, 2, 2]
def baseStart_2025905 : Nat := 118140960795 + 2025905 * 2 ^ 59
def prefixEnd_2025905 : Nat := 4983230072969 + 3 ^ 40 * 2025905 * 2
def baseEnd_2025905 : Nat := 1040263025347001371070539

theorem tailTrace_2025905 : CollatzResearch.WordTrace tailWord_2025905 prefixEnd_2025905 1040263025347001371070539 := by
  unfold tailWord_2025905
  simp only [CollatzResearch.WordTrace]
  refine ⟨73890825725499656872879169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49260550483666437915252779 73890825725499656872879169)
  ·
    refine ⟨55418119294124742654659377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73890825725499656872879169 55418119294124742654659377)
    ·
      refine ⟨41563589470593556990994533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55418119294124742654659377 41563589470593556990994533)
      ·
        refine ⟨7793173025736291935811475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41563589470593556990994533 7793173025736291935811475)
        ·
          refine ⟨11689759538604437903717213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793173025736291935811475 11689759538604437903717213)
          ·
            refine ⟨4383659826976664213893955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11689759538604437903717213 4383659826976664213893955)
            ·
              refine ⟨6575489740464996320840933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383659826976664213893955 6575489740464996320840933)
              ·
                refine ⟨1232904326337186810157675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6575489740464996320840933 1232904326337186810157675)
                ·
                  refine ⟨1849356489505780215236513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1232904326337186810157675 1849356489505780215236513)
                  ·
                    refine ⟨1387017367129335161427385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1849356489505780215236513 1387017367129335161427385)
                    ·
                      refine ⟨1040263025347001371070539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387017367129335161427385 1040263025347001371070539)
                      ·
                        rfl

theorem cell23_2025905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_2025905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025905 prefixEnd_2025905 := by exact prefixLift 2025905
  have htrace : WordTrace (prefixWord ++ tailWord_2025905) baseStart_2025905 baseEnd_2025905 := by
    simpa [prefixWord, tailWord_2025905, baseEnd_2025905] using wordTrace_append hprefix tailTrace_2025905
  have hstable : (prefixWord ++ tailWord_2025905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025905).length < 2 ^ (prefixWord ++ tailWord_2025905).sum := by decide
  have hdescent : baseEnd_2025905 < baseStart_2025905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025931 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 1, 3, 2]
def baseStart_2025931 : Nat := 118140960795 + 2025931 * 2 ^ 59
def prefixEnd_2025931 : Nat := 4983230072969 + 3 ^ 40 * 2025931 * 2
def baseEnd_2025931 : Nat := 1040276375844018269345419

theorem tailTrace_2025931 : CollatzResearch.WordTrace tailWord_2025931 prefixEnd_2025931 1040276375844018269345419 := by
  unfold tailWord_2025931
  simp only [CollatzResearch.WordTrace]
  refine ⟨73891774023405463313325647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49261182682270308875550431 73891774023405463313325647)
  ·
    refine ⟨110837661035108194969988471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73891774023405463313325647 110837661035108194969988471)
    ·
      refine ⟨166256491552662292454982707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110837661035108194969988471 166256491552662292454982707)
      ·
        refine ⟨249384737328993438682474061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166256491552662292454982707 249384737328993438682474061)
        ·
          refine ⟨93519276498372539505927773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249384737328993438682474061 93519276498372539505927773)
          ·
            refine ⟨35069728686889702314722915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93519276498372539505927773 35069728686889702314722915)
            ·
              refine ⟨52604593030334553472084373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35069728686889702314722915 52604593030334553472084373)
              ·
                refine ⟨2465840298296932194003955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52604593030334553472084373 2465840298296932194003955)
                ·
                  refine ⟨3698760447445398291005933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2465840298296932194003955 3698760447445398291005933)
                  ·
                    refine ⟨1387035167792024359127225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3698760447445398291005933 1387035167792024359127225)
                    ·
                      refine ⟨1040276375844018269345419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387035167792024359127225 1040276375844018269345419)
                      ·
                        rfl

theorem cell23_2025931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 3, 2].length) (baseStart_2025931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025931 prefixEnd_2025931 := by exact prefixLift 2025931
  have htrace : WordTrace (prefixWord ++ tailWord_2025931) baseStart_2025931 baseEnd_2025931 := by
    simpa [prefixWord, tailWord_2025931, baseEnd_2025931] using wordTrace_append hprefix tailTrace_2025931
  have hstable : (prefixWord ++ tailWord_2025931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025931).length < 2 ^ (prefixWord ++ tailWord_2025931).sum := by decide
  have hdescent : baseEnd_2025931 < baseStart_2025931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2025955 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2025955 : Nat := 118140960795 + 2025955 * 2 ^ 59
def prefixEnd_2025955 : Nat := 4983230072969 + 3 ^ 40 * 2025955 * 2
def baseEnd_2025955 : Nat := 1040288699379726175445309

theorem tailTrace_2025955 : CollatzResearch.WordTrace tailWord_2025955 prefixEnd_2025955 1040288699379726175445309 := by
  unfold tailWord_2025955
  simp only [CollatzResearch.WordTrace]
  refine ⟨73892649375318515412199319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49261766250212343608132879 73892649375318515412199319)
  ·
    refine ⟨110838974062977773118298979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73892649375318515412199319 110838974062977773118298979)
    ·
      refine ⟨166258461094466659677448469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110838974062977773118298979 166258461094466659677448469)
      ·
        refine ⟨7793365363803124672380397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166258461094466659677448469 7793365363803124672380397)
        ·
          refine ⟨2922512011426171752142649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7793365363803124672380397 2922512011426171752142649)
          ·
            refine ⟨2191884008569628814106987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922512011426171752142649 2191884008569628814106987)
            ·
              refine ⟨3287826012854443221160481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2191884008569628814106987 3287826012854443221160481)
              ·
                refine ⟨2465869509640832415870361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3287826012854443221160481 2465869509640832415870361)
                ·
                  refine ⟨1849402132230624311902771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2465869509640832415870361 1849402132230624311902771)
                  ·
                    refine ⟨2774103198345936467854157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1849402132230624311902771 2774103198345936467854157)
                    ·
                      refine ⟨1040288699379726175445309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2774103198345936467854157 1040288699379726175445309)
                      ·
                        rfl

theorem cell23_2025955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2025955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2025955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2025955 prefixEnd_2025955 := by exact prefixLift 2025955
  have htrace : WordTrace (prefixWord ++ tailWord_2025955) baseStart_2025955 baseEnd_2025955 := by
    simpa [prefixWord, tailWord_2025955, baseEnd_2025955] using wordTrace_append hprefix tailTrace_2025955
  have hstable : (prefixWord ++ tailWord_2025955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2025955).length < 2 ^ (prefixWord ++ tailWord_2025955).sum := by decide
  have hdescent : baseEnd_2025955 < baseStart_2025955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2025955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026034 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2026034 : Nat := 118140960795 + 2026034 * 2 ^ 59
def prefixEnd_2026034 : Nat := 4983230072969 + 3 ^ 40 * 2026034 * 2
def baseEnd_2026034 : Nat := 1040329264351431366357445

theorem tailTrace_2026034 : CollatzResearch.WordTrace tailWord_2026034 prefixEnd_2026034 1040329264351431366357445 := by
  unfold tailWord_2026034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473882685508077976081289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49263687161354874602883437 18473882685508077976081289)
  ·
    refine ⟨13855412014131058482060967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18473882685508077976081289 13855412014131058482060967)
    ·
      refine ⟨20783118021196587723091451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13855412014131058482060967 20783118021196587723091451)
      ·
        refine ⟨31174677031794881584637177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20783118021196587723091451 31174677031794881584637177)
        ·
          refine ⟨23381007773846161188477883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31174677031794881584637177 23381007773846161188477883)
          ·
            refine ⟨35071511660769241782716825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23381007773846161188477883 35071511660769241782716825)
            ·
              refine ⟨26303633745576931337037619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35071511660769241782716825 26303633745576931337037619)
              ·
                refine ⟨39455450618365397005556429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26303633745576931337037619 39455450618365397005556429)
                ·
                  refine ⟨14795793981887023877083661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39455450618365397005556429 14795793981887023877083661)
                  ·
                    refine ⟨5548422743207633953906373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14795793981887023877083661 5548422743207633953906373)
                    ·
                      refine ⟨1040329264351431366357445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5548422743207633953906373 1040329264351431366357445)
                      ·
                        rfl

theorem cell23_2026034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2026034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026034 prefixEnd_2026034 := by exact prefixLift 2026034
  have htrace : WordTrace (prefixWord ++ tailWord_2026034) baseStart_2026034 baseEnd_2026034 := by
    simpa [prefixWord, tailWord_2026034, baseEnd_2026034] using wordTrace_append hprefix tailTrace_2026034
  have hstable : (prefixWord ++ tailWord_2026034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026034).length < 2 ^ (prefixWord ++ tailWord_2026034).sum := by decide
  have hdescent : baseEnd_2026034 < baseStart_2026034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026071 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_2026071 : Nat := 118140960795 + 2026071 * 2 ^ 59
def prefixEnd_2026071 : Nat := 4983230072969 + 3 ^ 40 * 2026071 * 2
def baseEnd_2026071 : Nat := 1040348263135647721594775

theorem tailTrace_2026071 : CollatzResearch.WordTrace tailWord_2026071 prefixEnd_2026071 1040348263135647721594775 := by
  unfold tailWord_2026071
  simp only [CollatzResearch.WordTrace]
  refine ⟨73896880242898267223422067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49264586828598844815614711 73896880242898267223422067)
  ·
    refine ⟨110845320364347400835133101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73896880242898267223422067 110845320364347400835133101)
    ·
      refine ⟨41566995136630275313174913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110845320364347400835133101 41566995136630275313174913)
      ·
        refine ⟨31175246352472706484881185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41566995136630275313174913 31175246352472706484881185)
        ·
          refine ⟨23381434764354529863660889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31175246352472706484881185 23381434764354529863660889)
          ·
            refine ⟨17536076073265897397745667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23381434764354529863660889 17536076073265897397745667)
            ·
              refine ⟨26304114109898846096618501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17536076073265897397745667 26304114109898846096618501)
              ·
                refine ⟨4932021395606033643115969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26304114109898846096618501 4932021395606033643115969)
                ·
                  refine ⟨3699016046704525232336977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4932021395606033643115969 3699016046704525232336977)
                  ·
                    refine ⟨2774262035028393924252733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3699016046704525232336977 2774262035028393924252733)
                    ·
                      refine ⟨1040348263135647721594775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2774262035028393924252733 1040348263135647721594775)
                      ·
                        rfl

theorem cell23_2026071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_2026071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026071 prefixEnd_2026071 := by exact prefixLift 2026071
  have htrace : WordTrace (prefixWord ++ tailWord_2026071) baseStart_2026071 baseEnd_2026071 := by
    simpa [prefixWord, tailWord_2026071, baseEnd_2026071] using wordTrace_append hprefix tailTrace_2026071
  have hstable : (prefixWord ++ tailWord_2026071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026071).length < 2 ^ (prefixWord ++ tailWord_2026071).sum := by decide
  have hdescent : baseEnd_2026071 < baseStart_2026071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026102 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4]
def baseStart_2026102 : Nat := 118140960795 + 2026102 * 2 ^ 59
def prefixEnd_2026102 : Nat := 4983230072969 + 3 ^ 40 * 2026102 * 2
def baseEnd_2026102 : Nat := 1040364181035937100307133

theorem tailTrace_2026102 : CollatzResearch.WordTrace tailWord_2026102 prefixEnd_2026102 1040364181035937100307133 := by
  unfold tailWord_2026102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618625681611622469862535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49265340603857306345200373 4618625681611622469862535)
  ·
    refine ⟨6927938522417433704793803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618625681611622469862535 6927938522417433704793803)
    ·
      refine ⟨10391907783626150557190705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927938522417433704793803 10391907783626150557190705)
      ·
        refine ⟨7793930837719612917893029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10391907783626150557190705 7793930837719612917893029)
        ·
          refine ⟨1461362032072427422104943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7793930837719612917893029 1461362032072427422104943)
          ·
            refine ⟨2192043048108641133157415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461362032072427422104943 2192043048108641133157415)
            ·
              refine ⟨3288064572162961699736123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192043048108641133157415 3288064572162961699736123)
              ·
                refine ⟨4932096858244442549604185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288064572162961699736123 4932096858244442549604185)
                ·
                  refine ⟨3699072643683331912203139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4932096858244442549604185 3699072643683331912203139)
                  ·
                    refine ⟨5548608965524997868304709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3699072643683331912203139 5548608965524997868304709)
                    ·
                      refine ⟨1040364181035937100307133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5548608965524997868304709 1040364181035937100307133)
                      ·
                        rfl

theorem cell23_2026102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_2026102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026102 prefixEnd_2026102 := by exact prefixLift 2026102
  have htrace : WordTrace (prefixWord ++ tailWord_2026102) baseStart_2026102 baseEnd_2026102 := by
    simpa [prefixWord, tailWord_2026102, baseEnd_2026102] using wordTrace_append hprefix tailTrace_2026102
  have hstable : (prefixWord ++ tailWord_2026102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026102).length < 2 ^ (prefixWord ++ tailWord_2026102).sum := by decide
  have hdescent : baseEnd_2026102 < baseStart_2026102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026135 : List Nat := [1, 1, 3, 3, 2, 1, 1, 6, 1, 1, 3]
def baseStart_2026135 : Nat := 118140960795 + 2026135 * 2 ^ 59
def prefixEnd_2026135 : Nat := 4983230072969 + 3 ^ 40 * 2026135 * 2
def baseEnd_2026135 : Nat := 1040381125897535471194481

theorem tailTrace_2026135 : CollatzResearch.WordTrace tailWord_2026135 prefixEnd_2026135 1040381125897535471194481 := by
  unfold tailWord_2026135
  simp only [CollatzResearch.WordTrace]
  refine ⟨73899214514666406153751859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49266143009777604102501239 73899214514666406153751859)
  ·
    refine ⟨110848821771999609230627789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73899214514666406153751859 110848821771999609230627789)
    ·
      refine ⟨41568308164499853461485421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110848821771999609230627789 41568308164499853461485421)
      ·
        refine ⟨15588115561687445048057033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41568308164499853461485421 15588115561687445048057033)
        ·
          refine ⟨11691086671265583786042775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15588115561687445048057033 11691086671265583786042775)
          ·
            refine ⟨17536630006898375679064163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11691086671265583786042775 17536630006898375679064163)
            ·
              refine ⟨26304945010347563518596245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17536630006898375679064163 26304945010347563518596245)
              ·
                refine ⟨1233044297360042039934199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26304945010347563518596245 1233044297360042039934199)
                ·
                  refine ⟨1849566446040063059901299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1233044297360042039934199 1849566446040063059901299)
                  ·
                    refine ⟨2774349669060094589851949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1849566446040063059901299 2774349669060094589851949)
                    ·
                      refine ⟨1040381125897535471194481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2774349669060094589851949 1040381125897535471194481)
                      ·
                        rfl

theorem cell23_2026135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_2026135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026135 prefixEnd_2026135 := by exact prefixLift 2026135
  have htrace : WordTrace (prefixWord ++ tailWord_2026135) baseStart_2026135 baseEnd_2026135 := by
    simpa [prefixWord, tailWord_2026135, baseEnd_2026135] using wordTrace_append hprefix tailTrace_2026135
  have hstable : (prefixWord ++ tailWord_2026135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026135).length < 2 ^ (prefixWord ++ tailWord_2026135).sum := by decide
  have hdescent : baseEnd_2026135 < baseStart_2026135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026141 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2026141 : Nat := 118140960795 + 2026141 * 2 ^ 59
def prefixEnd_2026141 : Nat := 4983230072969 + 3 ^ 40 * 2026141 * 2
def baseEnd_2026141 : Nat := 1040384206781462447719453

theorem tailTrace_2026141 : CollatzResearch.WordTrace tailWord_2026141 prefixEnd_2026141 1040384206781462447719453 := by
  unfold tailWord_2026141
  simp only [CollatzResearch.WordTrace]
  refine ⟨73899433352644669178470277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49266288901763112785646851 73899433352644669178470277)
  ·
    refine ⟨13856143753620875470963177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73899433352644669178470277 13856143753620875470963177)
    ·
      refine ⟨10392107815215656603222383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13856143753620875470963177 10392107815215656603222383)
      ·
        refine ⟨15588161722823484904833575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10392107815215656603222383 15588161722823484904833575)
        ·
          refine ⟨23382242584235227357250363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15588161722823484904833575 23382242584235227357250363)
          ·
            refine ⟨35073363876352841035875545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23382242584235227357250363 35073363876352841035875545)
            ·
              refine ⟨26305022907264630776906659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35073363876352841035875545 26305022907264630776906659)
              ·
                refine ⟨39457534360896946165359989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26305022907264630776906659 39457534360896946165359989)
                ·
                  refine ⟨3699143846334088703002499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39457534360896946165359989 3699143846334088703002499)
                  ·
                    refine ⟨5548715769501133054503749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3699143846334088703002499 5548715769501133054503749)
                    ·
                      refine ⟨1040384206781462447719453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5548715769501133054503749 1040384206781462447719453)
                      ·
                        rfl

theorem cell23_2026141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2026141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026141 prefixEnd_2026141 := by exact prefixLift 2026141
  have htrace : WordTrace (prefixWord ++ tailWord_2026141) baseStart_2026141 baseEnd_2026141 := by
    simpa [prefixWord, tailWord_2026141, baseEnd_2026141] using wordTrace_append hprefix tailTrace_2026141
  have hstable : (prefixWord ++ tailWord_2026141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026141).length < 2 ^ (prefixWord ++ tailWord_2026141).sum := by decide
  have hdescent : baseEnd_2026141 < baseStart_2026141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026229 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2026229 : Nat := 118140960795 + 2026229 * 2 ^ 59
def prefixEnd_2026229 : Nat := 4983230072969 + 3 ^ 40 * 2026229 * 2
def baseEnd_2026229 : Nat := 1040429393079058103419049

theorem tailTrace_2026229 : CollatzResearch.WordTrace tailWord_2026229 prefixEnd_2026229 1040429393079058103419049 := by
  unfold tailWord_2026229
  simp only [CollatzResearch.WordTrace]
  refine ⟨73902642976325860207673741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49268428650883906805115827 73902642976325860207673741)
  ·
    refine ⟨27713491116122197577877653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73902642976325860207673741 27713491116122197577877653)
    ·
      refine ⟨1299069896068228011463015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27713491116122197577877653 1299069896068228011463015)
      ·
        refine ⟨1948604844102342017194523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1299069896068228011463015 1948604844102342017194523)
        ·
          refine ⟨2922907266153513025791785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1948604844102342017194523 2922907266153513025791785)
          ·
            refine ⟨2192180449615134769343839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2922907266153513025791785 2192180449615134769343839)
            ·
              refine ⟨3288270674422702154015759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192180449615134769343839 3288270674422702154015759)
              ·
                refine ⟨4932406011634053231023639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288270674422702154015759 4932406011634053231023639)
                ·
                  refine ⟨7398609017451079846535459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932406011634053231023639 7398609017451079846535459)
                  ·
                    refine ⟨11097913526176619769803189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7398609017451079846535459 11097913526176619769803189)
                    ·
                      refine ⟨1040429393079058103419049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11097913526176619769803189 1040429393079058103419049)
                      ·
                        rfl

theorem cell23_2026229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2026229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026229 prefixEnd_2026229 := by exact prefixLift 2026229
  have htrace : WordTrace (prefixWord ++ tailWord_2026229) baseStart_2026229 baseEnd_2026229 := by
    simpa [prefixWord, tailWord_2026229, baseEnd_2026229] using wordTrace_append hprefix tailTrace_2026229
  have hstable : (prefixWord ++ tailWord_2026229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026229).length < 2 ^ (prefixWord ++ tailWord_2026229).sum := by decide
  have hdescent : baseEnd_2026229 < baseStart_2026229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026241 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2026241 : Nat := 118140960795 + 2026241 * 2 ^ 59
def prefixEnd_2026241 : Nat := 4983230072969 + 3 ^ 40 * 2026241 * 2
def baseEnd_2026241 : Nat := 346811851615637352156331

theorem tailTrace_2026241 : CollatzResearch.WordTrace tailWord_2026241 prefixEnd_2026241 346811851615637352156331 := by
  unfold tailWord_2026241
  simp only [CollatzResearch.WordTrace]
  refine ⟨73903080652282386257110577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49268720434854924171407051 73903080652282386257110577)
  ·
    refine ⟨55427310489211789692832933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73903080652282386257110577 55427310489211789692832933)
    ·
      refine ⟨10392620716727210567406175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55427310489211789692832933 10392620716727210567406175)
      ·
        refine ⟨15588931075090815851109263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10392620716727210567406175 15588931075090815851109263)
        ·
          refine ⟨23383396612636223776663895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15588931075090815851109263 23383396612636223776663895)
          ·
            refine ⟨35075094918954335664995843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23383396612636223776663895 35075094918954335664995843)
            ·
              refine ⟨52612642378431503497493765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35075094918954335664995843 52612642378431503497493765)
              ·
                refine ⟨9864870445955906905780081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52612642378431503497493765 9864870445955906905780081)
                ·
                  refine ⟨7398652834466930179335061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9864870445955906905780081 7398652834466930179335061)
                  ·
                    refine ⟨346811851615637352156331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7398652834466930179335061 346811851615637352156331)
                    ·
                      rfl

theorem cell23_2026241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2026241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026241 prefixEnd_2026241 := by exact prefixLift 2026241
  have htrace : WordTrace (prefixWord ++ tailWord_2026241) baseStart_2026241 baseEnd_2026241 := by
    simpa [prefixWord, tailWord_2026241, baseEnd_2026241] using wordTrace_append hprefix tailTrace_2026241
  have hstable : (prefixWord ++ tailWord_2026241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026241).length < 2 ^ (prefixWord ++ tailWord_2026241).sum := by decide
  have hdescent : baseEnd_2026241 < baseStart_2026241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026242 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2026242 : Nat := 118140960795 + 2026242 * 2 ^ 59
def prefixEnd_2026242 : Nat := 4983230072969 + 3 ^ 40 * 2026242 * 2
def baseEnd_2026242 : Nat := 1040436068327566552556489

theorem tailTrace_2026242 : CollatzResearch.WordTrace tailWord_2026242 prefixEnd_2026242 1040436068327566552556489 := by
  unfold tailWord_2026242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475779281319690856974245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49268744750185842285264653 18475779281319690856974245)
  ·
    refine ⟨3464208615247442035682671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18475779281319690856974245 3464208615247442035682671)
    ·
      refine ⟨5196312922871163053524007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464208615247442035682671 5196312922871163053524007)
      ·
        refine ⟨7794469384306744580286011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196312922871163053524007 7794469384306744580286011)
        ·
          refine ⟨11691704076460116870429017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7794469384306744580286011 11691704076460116870429017)
          ·
            refine ⟨8768778057345087652821763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11691704076460116870429017 8768778057345087652821763)
            ·
              refine ⟨13153167086017631479232645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768778057345087652821763 13153167086017631479232645)
              ·
                refine ⟨2466218828628305902356121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13153167086017631479232645 2466218828628305902356121)
                ·
                  refine ⟨1849664121471229426767091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2466218828628305902356121 1849664121471229426767091)
                  ·
                    refine ⟨2774496182206844140150637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1849664121471229426767091 2774496182206844140150637)
                    ·
                      refine ⟨1040436068327566552556489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2774496182206844140150637 1040436068327566552556489)
                      ·
                        rfl

theorem cell23_2026242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2026242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026242 prefixEnd_2026242 := by exact prefixLift 2026242
  have htrace : WordTrace (prefixWord ++ tailWord_2026242) baseStart_2026242 baseEnd_2026242 := by
    simpa [prefixWord, tailWord_2026242, baseEnd_2026242] using wordTrace_append hprefix tailTrace_2026242
  have hstable : (prefixWord ++ tailWord_2026242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026242).length < 2 ^ (prefixWord ++ tailWord_2026242).sum := by decide
  have hdescent : baseEnd_2026242 < baseStart_2026242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026271 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 9]
def baseStart_2026271 : Nat := 118140960795 + 2026271 * 2 ^ 59
def prefixEnd_2026271 : Nat := 4983230072969 + 3 ^ 40 * 2026271 * 2
def baseEnd_2026271 : Nat := 115605662140727437677095

theorem tailTrace_2026271 : CollatzResearch.WordTrace tailWord_2026271 prefixEnd_2026271 115605662140727437677095 := by
  unfold tailWord_2026271
  simp only [CollatzResearch.WordTrace]
  refine ⟨73904174842173701380702667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49269449894782467587135111 73904174842173701380702667)
  ·
    refine ⟨110856262263260552071054001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73904174842173701380702667 110856262263260552071054001)
    ·
      refine ⟨83142196697445414053290501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110856262263260552071054001 83142196697445414053290501)
      ·
        refine ⟨15589161880771015134991969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83142196697445414053290501 15589161880771015134991969)
        ·
          refine ⟨11691871410578261351243977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15589161880771015134991969 11691871410578261351243977)
          ·
            refine ⟨8768903557933696013432983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11691871410578261351243977 8768903557933696013432983)
            ·
              refine ⟨13153355336900544020149475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768903557933696013432983 13153355336900544020149475)
              ·
                refine ⟨19730033005350816030224213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13153355336900544020149475 19730033005350816030224213)
                ·
                  refine ⟨115605662140727437677095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19730033005350816030224213 115605662140727437677095)
                  ·
                    rfl

theorem cell23_2026271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 9].length) (baseStart_2026271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026271 prefixEnd_2026271 := by exact prefixLift 2026271
  have htrace : WordTrace (prefixWord ++ tailWord_2026271) baseStart_2026271 baseEnd_2026271 := by
    simpa [prefixWord, tailWord_2026271, baseEnd_2026271] using wordTrace_append hprefix tailTrace_2026271
  have hstable : (prefixWord ++ tailWord_2026271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026271).length < 2 ^ (prefixWord ++ tailWord_2026271).sum := by decide
  have hdescent : baseEnd_2026271 < baseStart_2026271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026286 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2026286 : Nat := 118140960795 + 2026286 * 2 ^ 59
def prefixEnd_2026286 : Nat := 4983230072969 + 3 ^ 40 * 2026286 * 2
def baseEnd_2026286 : Nat := 1040458661476364380406287

theorem tailTrace_2026286 : CollatzResearch.WordTrace tailWord_2026286 prefixEnd_2026286 1040458661476364380406287 := by
  unfold tailWord_2026286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238090242139919867812339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49269814624746239294999141 9238090242139919867812339)
  ·
    refine ⟨13857135363209879801718509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9238090242139919867812339 13857135363209879801718509)
    ·
      refine ⟨5196425761203704925644441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13857135363209879801718509 5196425761203704925644441)
      ·
        refine ⟨3897319320902778694233331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5196425761203704925644441 3897319320902778694233331)
        ·
          refine ⟨5845978981354168041349997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897319320902778694233331 5845978981354168041349997)
          ·
            refine ⟨2192242118007813015506249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5845978981354168041349997 2192242118007813015506249)
            ·
              refine ⟨1644181588505859761629687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192242118007813015506249 1644181588505859761629687)
              ·
                refine ⟨2466272382758789642444531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644181588505859761629687 2466272382758789642444531)
                ·
                  refine ⟨3699408574138184463666797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466272382758789642444531 3699408574138184463666797)
                  ·
                    refine ⟨1387278215301819173875049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699408574138184463666797 1387278215301819173875049)
                    ·
                      refine ⟨1040458661476364380406287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387278215301819173875049 1040458661476364380406287)
                      ·
                        rfl

theorem cell23_2026286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2026286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026286 prefixEnd_2026286 := by exact prefixLift 2026286
  have htrace : WordTrace (prefixWord ++ tailWord_2026286) baseStart_2026286 baseEnd_2026286 := by
    simpa [prefixWord, tailWord_2026286, baseEnd_2026286] using wordTrace_append hprefix tailTrace_2026286
  have hstable : (prefixWord ++ tailWord_2026286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026286).length < 2 ^ (prefixWord ++ tailWord_2026286).sum := by decide
  have hdescent : baseEnd_2026286 < baseStart_2026286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026311 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_2026311 : Nat := 118140960795 + 2026311 * 2 ^ 59
def prefixEnd_2026311 : Nat := 4983230072969 + 3 ^ 40 * 2026311 * 2
def baseEnd_2026311 : Nat := 1040471498492726782593671

theorem tailTrace_2026311 : CollatzResearch.WordTrace tailWord_2026311 prefixEnd_2026311 1040471498492726782593671 := by
  unfold tailWord_2026311
  simp only [CollatzResearch.WordTrace]
  refine ⟨73905633762028788212158787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49270422508019192141439191 73905633762028788212158787)
  ·
    refine ⟨110858450643043182318238181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73905633762028788212158787 110858450643043182318238181)
    ·
      refine ⟨20785959495570596684669659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110858450643043182318238181 20785959495570596684669659)
      ·
        refine ⟨31178939243355895027004489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20785959495570596684669659 31178939243355895027004489)
        ·
          refine ⟨23384204432516921270253367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31178939243355895027004489 23384204432516921270253367)
          ·
            refine ⟨35076306648775381905380051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23384204432516921270253367 35076306648775381905380051)
            ·
              refine ⟨52614459973163072858070077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35076306648775381905380051 52614459973163072858070077)
              ·
                refine ⟨19730422489936152321776279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52614459973163072858070077 19730422489936152321776279)
                ·
                  refine ⟨29595633734904228482664419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19730422489936152321776279 29595633734904228482664419)
                  ·
                    refine ⟨44393450602356342723996629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29595633734904228482664419 44393450602356342723996629)
                    ·
                      refine ⟨1040471498492726782593671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44393450602356342723996629 1040471498492726782593671)
                      ·
                        rfl

theorem cell23_2026311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_2026311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026311 prefixEnd_2026311 := by exact prefixLift 2026311
  have htrace : WordTrace (prefixWord ++ tailWord_2026311) baseStart_2026311 baseEnd_2026311 := by
    simpa [prefixWord, tailWord_2026311, baseEnd_2026311] using wordTrace_append hprefix tailTrace_2026311
  have hstable : (prefixWord ++ tailWord_2026311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026311).length < 2 ^ (prefixWord ++ tailWord_2026311).sum := by decide
  have hdescent : baseEnd_2026311 < baseStart_2026311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026351 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 6]
def baseStart_2026351 : Nat := 118140960795 + 2026351 * 2 ^ 59
def prefixEnd_2026351 : Nat := 4983230072969 + 3 ^ 40 * 2026351 * 2
def baseEnd_2026351 : Nat := 1040492037718906626093487

theorem tailTrace_2026351 : CollatzResearch.WordTrace tailWord_2026351 prefixEnd_2026351 1040492037718906626093487 := by
  unfold tailWord_2026351
  simp only [CollatzResearch.WordTrace]
  refine ⟨73907092681883875043614907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49271395121255916695743271 73907092681883875043614907)
  ·
    refine ⟨110860639022825812565422361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73907092681883875043614907 110860639022825812565422361)
    ·
      refine ⟨83145479267119359424066771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110860639022825812565422361 83145479267119359424066771)
      ·
        refine ⟨124718218900679039136100157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83145479267119359424066771 124718218900679039136100157)
        ·
          refine ⟨46769332087754639676037559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124718218900679039136100157 46769332087754639676037559)
          ·
            refine ⟨70153998131631959514056339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46769332087754639676037559 70153998131631959514056339)
            ·
              refine ⟨105230997197447939271084509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70153998131631959514056339 105230997197447939271084509)
              ·
                refine ⟨39461623949042977226656691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105230997197447939271084509 39461623949042977226656691)
                ·
                  refine ⟨59192435923564465839985037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39461623949042977226656691 59192435923564465839985037)
                  ·
                    refine ⟨22197163471336674689994389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59192435923564465839985037 22197163471336674689994389)
                    ·
                      refine ⟨1040492037718906626093487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22197163471336674689994389 1040492037718906626093487)
                      ·
                        rfl

theorem cell23_2026351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_2026351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026351 prefixEnd_2026351 := by exact prefixLift 2026351
  have htrace : WordTrace (prefixWord ++ tailWord_2026351) baseStart_2026351 baseEnd_2026351 := by
    simpa [prefixWord, tailWord_2026351, baseEnd_2026351] using wordTrace_append hprefix tailTrace_2026351
  have hstable : (prefixWord ++ tailWord_2026351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026351).length < 2 ^ (prefixWord ++ tailWord_2026351).sum := by decide
  have hdescent : baseEnd_2026351 < baseStart_2026351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026365 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_2026365 : Nat := 118140960795 + 2026365 * 2 ^ 59
def prefixEnd_2026365 : Nat := 4983230072969 + 3 ^ 40 * 2026365 * 2
def baseEnd_2026365 : Nat := 346833075482689857106141

theorem tailTrace_2026365 : CollatzResearch.WordTrace tailWord_2026365 prefixEnd_2026365 346833075482689857106141 := by
  unfold tailWord_2026365
  simp only [CollatzResearch.WordTrace]
  refine ⟨73907603303833155434624549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49271735535888770289749699 73907603303833155434624549)
  ·
    refine ⟨13857675619468716643992103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73907603303833155434624549 13857675619468716643992103)
    ·
      refine ⟨20786513429203074965988155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13857675619468716643992103 20786513429203074965988155)
      ·
        refine ⟨31179770143804612448982233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20786513429203074965988155 31179770143804612448982233)
        ·
          refine ⟨23384827607853459336736675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31179770143804612448982233 23384827607853459336736675)
          ·
            refine ⟨35077241411780189005105013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23384827607853459336736675 35077241411780189005105013)
            ·
              refine ⟨3288491382354392719228595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35077241411780189005105013 3288491382354392719228595)
              ·
                refine ⟨4932737073531589078842893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288491382354392719228595 4932737073531589078842893)
                ·
                  refine ⟨1849776402574345904566085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4932737073531589078842893 1849776402574345904566085)
                  ·
                    refine ⟨346833075482689857106141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1849776402574345904566085 346833075482689857106141)
                    ·
                      rfl

theorem cell23_2026365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_2026365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026365 prefixEnd_2026365 := by exact prefixLift 2026365
  have htrace : WordTrace (prefixWord ++ tailWord_2026365) baseStart_2026365 baseEnd_2026365 := by
    simpa [prefixWord, tailWord_2026365, baseEnd_2026365] using wordTrace_append hprefix tailTrace_2026365
  have hstable : (prefixWord ++ tailWord_2026365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026365).length < 2 ^ (prefixWord ++ tailWord_2026365).sum := by decide
  have hdescent : baseEnd_2026365 < baseStart_2026365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026415 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 4, 3, 2]
def baseStart_2026415 : Nat := 118140960795 + 2026415 * 2 ^ 59
def prefixEnd_2026415 : Nat := 4983230072969 + 3 ^ 40 * 2026415 * 2
def baseEnd_2026415 : Nat := 1040524900480794375693193

theorem tailTrace_2026415 : CollatzResearch.WordTrace tailWord_2026415 prefixEnd_2026415 1040524900480794375693193 := by
  unfold tailWord_2026415
  simp only [CollatzResearch.WordTrace]
  refine ⟨73909426953652013973944699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49272951302434675982629799 73909426953652013973944699)
  ·
    refine ⟨110864140430478020960917049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73909426953652013973944699 110864140430478020960917049)
    ·
      refine ⟨83148105322858515720687787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110864140430478020960917049 83148105322858515720687787)
      ·
        refine ⟨124722157984287773581031681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83148105322858515720687787 124722157984287773581031681)
        ·
          refine ⟨93541618488215830185773761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124722157984287773581031681 93541618488215830185773761)
          ·
            refine ⟨70156213866161872639330321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93541618488215830185773761 70156213866161872639330321)
            ·
              refine ⟨52617160399621404479497741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70156213866161872639330321 52617160399621404479497741)
              ·
                refine ⟨19731435149858026679811653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52617160399621404479497741 19731435149858026679811653)
                ·
                  refine ⟨3699644090598380002464685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19731435149858026679811653 3699644090598380002464685)
                  ·
                    refine ⟨1387366533974392500924257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699644090598380002464685 1387366533974392500924257)
                    ·
                      refine ⟨1040524900480794375693193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387366533974392500924257 1040524900480794375693193)
                      ·
                        rfl

theorem cell23_2026415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3, 2].length) (baseStart_2026415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026415 prefixEnd_2026415 := by exact prefixLift 2026415
  have htrace : WordTrace (prefixWord ++ tailWord_2026415) baseStart_2026415 baseEnd_2026415 := by
    simpa [prefixWord, tailWord_2026415, baseEnd_2026415] using wordTrace_append hprefix tailTrace_2026415
  have hstable : (prefixWord ++ tailWord_2026415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026415).length < 2 ^ (prefixWord ++ tailWord_2026415).sum := by decide
  have hdescent : baseEnd_2026415 < baseStart_2026415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026472 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 2, 4]
def baseStart_2026472 : Nat := 118140960795 + 2026472 * 2 ^ 59
def prefixEnd_2026472 : Nat := 4983230072969 + 3 ^ 40 * 2026472 * 2
def baseEnd_2026472 : Nat := 346851389626033550893477

theorem tailTrace_2026472 : CollatzResearch.WordTrace tailWord_2026472 prefixEnd_2026472 346851389626033550893477 := by
  unfold tailWord_2026472
  simp only [CollatzResearch.WordTrace]
  refine ⟨36955752957222756354384835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49274337276297008472513113 36955752957222756354384835)
  ·
    refine ⟨55433629435834134531577253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36955752957222756354384835 55433629435834134531577253)
    ·
      refine ⟨10393805519218900224670735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55433629435834134531577253 10393805519218900224670735)
      ·
        refine ⟨15590708278828350337006103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10393805519218900224670735 15590708278828350337006103)
        ·
          refine ⟨23386062418242525505509155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15590708278828350337006103 23386062418242525505509155)
          ·
            refine ⟨35079093627363788258263733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23386062418242525505509155 35079093627363788258263733)
            ·
              refine ⟨3288665027565355149212225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35079093627363788258263733 3288665027565355149212225)
              ·
                refine ⟨2466498770674016361909169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288665027565355149212225 2466498770674016361909169)
                ·
                  refine ⟨1849874078005512271431877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2466498770674016361909169 1849874078005512271431877)
                  ·
                    refine ⟨346851389626033550893477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1849874078005512271431877 346851389626033550893477)
                    ·
                      rfl

theorem cell23_2026472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_2026472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026472 prefixEnd_2026472 := by exact prefixLift 2026472
  have htrace : WordTrace (prefixWord ++ tailWord_2026472) baseStart_2026472 baseEnd_2026472 := by
    simpa [prefixWord, tailWord_2026472, baseEnd_2026472] using wordTrace_append hprefix tailTrace_2026472
  have hstable : (prefixWord ++ tailWord_2026472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026472).length < 2 ^ (prefixWord ++ tailWord_2026472).sum := by decide
  have hdescent : baseEnd_2026472 < baseStart_2026472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026479 : List Nat := [1, 1, 2, 1, 4, 4, 2, 1, 3, 2, 2]
def baseStart_2026479 : Nat := 118140960795 + 2026479 * 2 ^ 59
def prefixEnd_2026479 : Nat := 4983230072969 + 3 ^ 40 * 2026479 * 2
def baseEnd_2026479 : Nat := 1040557763242682125292899

theorem tailTrace_2026479 : CollatzResearch.WordTrace tailWord_2026479 prefixEnd_2026479 1040557763242682125292899 := by
  unfold tailWord_2026479
  simp only [CollatzResearch.WordTrace]
  refine ⟨73911761225420152904274491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49274507483613435269516327 73911761225420152904274491)
  ·
    refine ⟨110867641838130229356411737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73911761225420152904274491 110867641838130229356411737)
    ·
      refine ⟨83150731378597672017308803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110867641838130229356411737 83150731378597672017308803)
      ·
        refine ⟨124726097067896508025963205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83150731378597672017308803 124726097067896508025963205)
        ·
          refine ⟨23386143200230595254868101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124726097067896508025963205 23386143200230595254868101)
          ·
            refine ⟨4384901850043236610287769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23386143200230595254868101 4384901850043236610287769)
            ·
              refine ⟨3288676387532427457715827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4384901850043236610287769 3288676387532427457715827)
              ·
                refine ⟨4933014581298641186573741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288676387532427457715827 4933014581298641186573741)
                ·
                  refine ⟨1849880467986990444965153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4933014581298641186573741 1849880467986990444965153)
                  ·
                    refine ⟨1387410350990242833723865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1849880467986990444965153 1387410350990242833723865)
                    ·
                      refine ⟨1040557763242682125292899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387410350990242833723865 1040557763242682125292899)
                      ·
                        rfl

theorem cell23_2026479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 2, 2].length) (baseStart_2026479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026479 prefixEnd_2026479 := by exact prefixLift 2026479
  have htrace : WordTrace (prefixWord ++ tailWord_2026479) baseStart_2026479 baseEnd_2026479 := by
    simpa [prefixWord, tailWord_2026479, baseEnd_2026479] using wordTrace_append hprefix tailTrace_2026479
  have hstable : (prefixWord ++ tailWord_2026479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026479).length < 2 ^ (prefixWord ++ tailWord_2026479).sum := by decide
  have hdescent : baseEnd_2026479 < baseStart_2026479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026492 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_2026492 : Nat := 118140960795 + 2026492 * 2 ^ 59
def prefixEnd_2026492 : Nat := 4983230072969 + 3 ^ 40 * 2026492 * 2
def baseEnd_2026492 : Nat := 1040564438491190574430339

theorem tailTrace_2026492 : CollatzResearch.WordTrace tailWord_2026492 prefixEnd_2026492 1040564438491190574430339 := by
  unfold tailWord_2026492
  simp only [CollatzResearch.WordTrace]
  refine ⟨36956117687186528062248865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49274823582915370749665153 36956117687186528062248865)
  ·
    refine ⟨27717088265389896046686649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36956117687186528062248865 27717088265389896046686649)
    ·
      refine ⟨20787816199042422035014987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27717088265389896046686649 20787816199042422035014987)
      ·
        refine ⟨31181724298563633052522481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20787816199042422035014987 31181724298563633052522481)
        ·
          refine ⟨23386293223922724789391861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31181724298563633052522481 23386293223922724789391861)
          ·
            refine ⟨2192464989742755449005487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23386293223922724789391861 2192464989742755449005487)
            ·
              refine ⟨3288697484614133173508231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192464989742755449005487 3288697484614133173508231)
              ·
                refine ⟨4933046226921199760262347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3288697484614133173508231 4933046226921199760262347)
                ·
                  refine ⟨7399569340381799640393521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933046226921199760262347 7399569340381799640393521)
                  ·
                    refine ⟨5549677005286349730295141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7399569340381799640393521 5549677005286349730295141)
                    ·
                      refine ⟨1040564438491190574430339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5549677005286349730295141 1040564438491190574430339)
                      ·
                        rfl

theorem cell23_2026492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_2026492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026492 prefixEnd_2026492 := by exact prefixLift 2026492
  have htrace : WordTrace (prefixWord ++ tailWord_2026492) baseStart_2026492 baseEnd_2026492 := by
    simpa [prefixWord, tailWord_2026492, baseEnd_2026492] using wordTrace_append hprefix tailTrace_2026492
  have hstable : (prefixWord ++ tailWord_2026492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026492).length < 2 ^ (prefixWord ++ tailWord_2026492).sum := by decide
  have hdescent : baseEnd_2026492 < baseStart_2026492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026505 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 7, 2]
def baseStart_2026505 : Nat := 118140960795 + 2026505 * 2 ^ 59
def prefixEnd_2026505 : Nat := 4983230072969 + 3 ^ 40 * 2026505 * 2
def baseEnd_2026505 : Nat := 1040571113739699023567779

theorem tailTrace_2026505 : CollatzResearch.WordTrace tailWord_2026505 prefixEnd_2026505 1040571113739699023567779 := by
  unfold tailWord_2026505
  simp only [CollatzResearch.WordTrace]
  refine ⟨73912709523325959344720969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49275139682217306229813979 73912709523325959344720969)
  ·
    refine ⟨55434532142494469508540727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73912709523325959344720969 55434532142494469508540727)
    ·
      refine ⟨83151798213741704262811091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55434532142494469508540727 83151798213741704262811091)
      ·
        refine ⟨124727697320612556394216637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83151798213741704262811091 124727697320612556394216637)
        ·
          refine ⟨46772886495229708647831239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124727697320612556394216637 46772886495229708647831239)
          ·
            refine ⟨70159329742844562971746859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46772886495229708647831239 70159329742844562971746859)
            ·
              refine ⟨105238994614266844457620289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70159329742844562971746859 105238994614266844457620289)
              ·
                refine ⟨78929245960700133343215217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105238994614266844457620289 78929245960700133343215217)
                ·
                  refine ⟨59196934470525100007411413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78929245960700133343215217 59196934470525100007411413)
                  ·
                    refine ⟨1387428151652932031423705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59196934470525100007411413 1387428151652932031423705)
                    ·
                      refine ⟨1040571113739699023567779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387428151652932031423705 1040571113739699023567779)
                      ·
                        rfl

theorem cell23_2026505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 7, 2].length) (baseStart_2026505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026505 prefixEnd_2026505 := by exact prefixLift 2026505
  have htrace : WordTrace (prefixWord ++ tailWord_2026505) baseStart_2026505 baseEnd_2026505 := by
    simpa [prefixWord, tailWord_2026505, baseEnd_2026505] using wordTrace_append hprefix tailTrace_2026505
  have hstable : (prefixWord ++ tailWord_2026505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026505).length < 2 ^ (prefixWord ++ tailWord_2026505).sum := by decide
  have hdescent : baseEnd_2026505 < baseStart_2026505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026556 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_2026556 : Nat := 118140960795 + 2026556 * 2 ^ 59
def prefixEnd_2026556 : Nat := 4983230072969 + 3 ^ 40 * 2026556 * 2
def baseEnd_2026556 : Nat := 1040597301253078324030045

theorem tailTrace_2026556 : CollatzResearch.WordTrace tailWord_2026556 prefixEnd_2026556 1040597301253078324030045 := by
  unfold tailWord_2026556
  simp only [CollatzResearch.WordTrace]
  refine ⟨36957284823070597527413761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49276379764094130036551681 36957284823070597527413761)
  ·
    refine ⟨27717963617302948145560321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36957284823070597527413761 27717963617302948145560321)
    ·
      refine ⟨20788472712977211109170241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27717963617302948145560321 20788472712977211109170241)
      ·
        refine ⟨15591354534732908331877681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20788472712977211109170241 15591354534732908331877681)
        ·
          refine ⟨11693515901049681248908261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15591354534732908331877681 11693515901049681248908261)
          ·
            refine ⟨2192534231446815234170299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11693515901049681248908261 2192534231446815234170299)
            ·
              refine ⟨3288801347170222851255449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2192534231446815234170299 3288801347170222851255449)
              ·
                refine ⟨2466601010377667138441587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3288801347170222851255449 2466601010377667138441587)
                ·
                  refine ⟨3699901515566500707662381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466601010377667138441587 3699901515566500707662381)
                  ·
                    refine ⟨1387463068337437765373393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699901515566500707662381 1387463068337437765373393)
                    ·
                      refine ⟨1040597301253078324030045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387463068337437765373393 1040597301253078324030045)
                      ·
                        rfl

theorem cell23_2026556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_2026556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026556 prefixEnd_2026556 := by exact prefixLift 2026556
  have htrace : WordTrace (prefixWord ++ tailWord_2026556) baseStart_2026556 baseEnd_2026556 := by
    simpa [prefixWord, tailWord_2026556, baseEnd_2026556] using wordTrace_append hprefix tailTrace_2026556
  have hstable : (prefixWord ++ tailWord_2026556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026556).length < 2 ^ (prefixWord ++ tailWord_2026556).sum := by decide
  have hdescent : baseEnd_2026556 < baseStart_2026556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026573 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_2026573 : Nat := 118140960795 + 2026573 * 2 ^ 59
def prefixEnd_2026573 : Nat := 4983230072969 + 3 ^ 40 * 2026573 * 2
def baseEnd_2026573 : Nat := 1040606030424204757517467

theorem tailTrace_2026573 : CollatzResearch.WordTrace tailWord_2026573 prefixEnd_2026573 1040606030424204757517467 := by
  unfold tailWord_2026573
  simp only [CollatzResearch.WordTrace]
  refine ⟨73915189687079606958196373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49276793124719737972130915 73915189687079606958196373)
  ·
    refine ⟨3464774516581856576165455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73915189687079606958196373 3464774516581856576165455)
    ·
      refine ⟨5197161774872784864248183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464774516581856576165455 5197161774872784864248183)
      ·
        refine ⟨7795742662309177296372275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197161774872784864248183 7795742662309177296372275)
        ·
          refine ⟨11693613993463765944558413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7795742662309177296372275 11693613993463765944558413)
          ·
            refine ⟨4385105247548912229209405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11693613993463765944558413 4385105247548912229209405)
            ·
              refine ⟨1644414467830842085953527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4385105247548912229209405 1644414467830842085953527)
              ·
                refine ⟨2466621701746263128930291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644414467830842085953527 2466621701746263128930291)
                ·
                  refine ⟨3699932552619394693395437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466621701746263128930291 3699932552619394693395437)
                  ·
                    refine ⟨1387474707232273010023289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3699932552619394693395437 1387474707232273010023289)
                    ·
                      refine ⟨1040606030424204757517467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387474707232273010023289 1040606030424204757517467)
                      ·
                        rfl

theorem cell23_2026573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_2026573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026573 prefixEnd_2026573 := by exact prefixLift 2026573
  have htrace : WordTrace (prefixWord ++ tailWord_2026573) baseStart_2026573 baseEnd_2026573 := by
    simpa [prefixWord, tailWord_2026573, baseEnd_2026573] using wordTrace_append hprefix tailTrace_2026573
  have hstable : (prefixWord ++ tailWord_2026573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026573).length < 2 ^ (prefixWord ++ tailWord_2026573).sum := by decide
  have hdescent : baseEnd_2026573 < baseStart_2026573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026592 : List Nat := [2, 1, 1, 3, 2, 2, 3, 4, 5]
def baseStart_2026592 : Nat := 118140960795 + 2026592 * 2 ^ 59
def prefixEnd_2026592 : Nat := 4983230072969 + 3 ^ 40 * 2026592 * 2
def baseEnd_2026592 : Nat := 115623976284071131464431

theorem tailTrace_2026592 : CollatzResearch.WordTrace tailWord_2026592 prefixEnd_2026592 115623976284071131464431 := by
  unfold tailWord_2026592
  simp only [CollatzResearch.WordTrace]
  refine ⟨36957941337005386601569015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49277255116007182135425353 36957941337005386601569015)
  ·
    refine ⟨55436912005508079902353523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36957941337005386601569015 55436912005508079902353523)
    ·
      refine ⟨83155368008262119853530285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55436912005508079902353523 83155368008262119853530285)
      ·
        refine ⟨31183263003098294945073857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83155368008262119853530285 31183263003098294945073857)
        ·
          refine ⟨23387447252323721208805393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31183263003098294945073857 23387447252323721208805393)
          ·
            refine ⟨17540585439242790906604045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23387447252323721208805393 17540585439242790906604045)
            ·
              refine ⟨6577719539716046589976517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17540585439242790906604045 6577719539716046589976517)
              ·
                refine ⟨1233322413696758735620597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6577719539716046589976517 1233322413696758735620597)
                ·
                  refine ⟨115623976284071131464431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1233322413696758735620597 115623976284071131464431)
                  ·
                    rfl

theorem cell23_2026592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 5].length) (baseStart_2026592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026592 prefixEnd_2026592 := by exact prefixLift 2026592
  have htrace : WordTrace (prefixWord ++ tailWord_2026592) baseStart_2026592 baseEnd_2026592 := by
    simpa [prefixWord, tailWord_2026592, baseEnd_2026592] using wordTrace_append hprefix tailTrace_2026592
  have hstable : (prefixWord ++ tailWord_2026592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026592).length < 2 ^ (prefixWord ++ tailWord_2026592).sum := by decide
  have hdescent : baseEnd_2026592 < baseStart_2026592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026602 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2026602 : Nat := 118140960795 + 2026602 * 2 ^ 59
def prefixEnd_2026602 : Nat := 4983230072969 + 3 ^ 40 * 2026602 * 2
def baseEnd_2026602 : Nat := 1040620921363185144054833

theorem tailTrace_2026602 : CollatzResearch.WordTrace tailWord_2026602 prefixEnd_2026602 1040620921363185144054833 := by
  unfold tailWord_2026602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18479061850993636227750515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49277498269316363274001373 18479061850993636227750515)
  ·
    refine ⟨27718592776490454341625773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18479061850993636227750515 27718592776490454341625773)
    ·
      refine ⟨10394472291183920378109665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27718592776490454341625773 10394472291183920378109665)
      ·
        refine ⟨7795854218387940283582249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10394472291183920378109665 7795854218387940283582249)
        ·
          refine ⟨5846890663790955212686687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7795854218387940283582249 5846890663790955212686687)
          ·
            refine ⟨8770335995686432819030031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846890663790955212686687 8770335995686432819030031)
            ·
              refine ⟨13155503993529649228545047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770335995686432819030031 13155503993529649228545047)
              ·
                refine ⟨19733255990294473842817571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13155503993529649228545047 19733255990294473842817571)
                ·
                  refine ⟨29599883985441710764226357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19733255990294473842817571 29599883985441710764226357)
                  ·
                    refine ⟨2774989123635160384146221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29599883985441710764226357 2774989123635160384146221)
                    ·
                      refine ⟨1040620921363185144054833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2774989123635160384146221 1040620921363185144054833)
                      ·
                        rfl

theorem cell23_2026602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2026602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026602 prefixEnd_2026602 := by exact prefixLift 2026602
  have htrace : WordTrace (prefixWord ++ tailWord_2026602) baseStart_2026602 baseEnd_2026602 := by
    simpa [prefixWord, tailWord_2026602, baseEnd_2026602] using wordTrace_append hprefix tailTrace_2026602
  have hstable : (prefixWord ++ tailWord_2026602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026602).length < 2 ^ (prefixWord ++ tailWord_2026602).sum := by decide
  have hdescent : baseEnd_2026602 < baseStart_2026602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026705 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_2026705 : Nat := 118140960795 + 2026705 * 2 ^ 59
def prefixEnd_2026705 : Nat := 4983230072969 + 3 ^ 40 * 2026705 * 2
def baseEnd_2026705 : Nat := 1040673809870598241066859

theorem tailTrace_2026705 : CollatzResearch.WordTrace tailWord_2026705 prefixEnd_2026705 1040673809870598241066859 := by
  unfold tailWord_2026705
  simp only [CollatzResearch.WordTrace]
  refine ⟨73920004122601393502001569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49280002748400929001334379 73920004122601393502001569)
  ·
    refine ⟨55440003091951045126501177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73920004122601393502001569 55440003091951045126501177)
    ·
      refine ⟨41580002318963283844875883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55440003091951045126501177 41580002318963283844875883)
      ·
        refine ⟨62370003478444925767313825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41580002318963283844875883 62370003478444925767313825)
        ·
          refine ⟨46777502608833694325485369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62370003478444925767313825 46777502608833694325485369)
          ·
            refine ⟨35083126956625270744114027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46777502608833694325485369 35083126956625270744114027)
            ·
              refine ⟨52624690434937906116171041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35083126956625270744114027 52624690434937906116171041)
              ·
                refine ⟨39468517826203429587128281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52624690434937906116171041 39468517826203429587128281)
                ·
                  refine ⟨29601388369652572190346211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39468517826203429587128281 29601388369652572190346211)
                  ·
                    refine ⟨44402082554478858285519317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29601388369652572190346211 44402082554478858285519317)
                    ·
                      refine ⟨1040673809870598241066859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44402082554478858285519317 1040673809870598241066859)
                      ·
                        rfl

theorem cell23_2026705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_2026705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026705 prefixEnd_2026705 := by exact prefixLift 2026705
  have htrace : WordTrace (prefixWord ++ tailWord_2026705) baseStart_2026705 baseEnd_2026705 := by
    simpa [prefixWord, tailWord_2026705, baseEnd_2026705] using wordTrace_append hprefix tailTrace_2026705
  have hstable : (prefixWord ++ tailWord_2026705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026705).length < 2 ^ (prefixWord ++ tailWord_2026705).sum := by decide
  have hdescent : baseEnd_2026705 < baseStart_2026705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026755 : List Nat := [1, 1, 1, 3, 2, 15]
def baseStart_2026755 : Nat := 118140960795 + 2026755 * 2 ^ 59
def prefixEnd_2026755 : Nat := 4983230072969 + 3 ^ 40 * 2026755 * 2
def baseEnd_2026755 : Nat := 4282713925528078376303

theorem tailTrace_2026755 : CollatzResearch.WordTrace tailWord_2026755 prefixEnd_2026755 4282713925528078376303 := by
  unfold tailWord_2026755
  simp only [CollatzResearch.WordTrace]
  refine ⟨73921827772420252041321719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49281218514946834694214479 73921827772420252041321719)
  ·
    refine ⟨110882741658630378061982579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73921827772420252041321719 110882741658630378061982579)
    ·
      refine ⟨166324112487945567092973869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110882741658630378061982579 166324112487945567092973869)
      ·
        refine ⟨62371542182979587659865201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166324112487945567092973869 62371542182979587659865201)
        ·
          refine ⟨46778656637234690744898901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62371542182979587659865201 46778656637234690744898901)
          ·
            refine ⟨4282713925528078376303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 46778656637234690744898901 4282713925528078376303)
            ·
              rfl

theorem cell23_2026755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 15].length) (baseStart_2026755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026755 prefixEnd_2026755 := by exact prefixLift 2026755
  have htrace : WordTrace (prefixWord ++ tailWord_2026755) baseStart_2026755 baseEnd_2026755 := by
    simpa [prefixWord, tailWord_2026755, baseEnd_2026755] using wordTrace_append hprefix tailTrace_2026755
  have hstable : (prefixWord ++ tailWord_2026755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026755).length < 2 ^ (prefixWord ++ tailWord_2026755).sum := by decide
  have hdescent : baseEnd_2026755 < baseStart_2026755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026762 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2026762 : Nat := 118140960795 + 2026762 * 2 ^ 59
def prefixEnd_2026762 : Nat := 4983230072969 + 3 ^ 40 * 2026762 * 2
def baseEnd_2026762 : Nat := 1040703078267904518054097

theorem tailTrace_2026762 : CollatzResearch.WordTrace tailWord_2026762 prefixEnd_2026762 1040703078267904518054097 := by
  unfold tailWord_2026762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480520770848723059206635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49281388722263261491217693 18480520770848723059206635)
  ·
    refine ⟨27720781156273084588809953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18480520770848723059206635 27720781156273084588809953)
    ·
      refine ⟨20790585867204813441607465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27720781156273084588809953 20790585867204813441607465)
      ·
        refine ⟨15592939400403610081205599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20790585867204813441607465 15592939400403610081205599)
        ·
          refine ⟨23389409100605415121808399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15592939400403610081205599 23389409100605415121808399)
          ·
            refine ⟨35084113650908122682712599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23389409100605415121808399 35084113650908122682712599)
            ·
              refine ⟨52626170476362184024068899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35084113650908122682712599 52626170476362184024068899)
              ·
                refine ⟨78939255714543276036103349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52626170476362184024068899 78939255714543276036103349)
                ·
                  refine ⟨7400555223238432128384689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78939255714543276036103349 7400555223238432128384689)
                  ·
                    refine ⟨5550416417428824096288517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7400555223238432128384689 5550416417428824096288517)
                    ·
                      refine ⟨1040703078267904518054097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5550416417428824096288517 1040703078267904518054097)
                      ·
                        rfl

theorem cell23_2026762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2026762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026762 prefixEnd_2026762 := by exact prefixLift 2026762
  have htrace : WordTrace (prefixWord ++ tailWord_2026762) baseStart_2026762 baseEnd_2026762 := by
    simpa [prefixWord, tailWord_2026762, baseEnd_2026762] using wordTrace_append hprefix tailTrace_2026762
  have hstable : (prefixWord ++ tailWord_2026762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026762).length < 2 ^ (prefixWord ++ tailWord_2026762).sum := by decide
  have hdescent : baseEnd_2026762 < baseStart_2026762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026783 : List Nat := [1, 1, 2, 4, 4, 1, 1, 2, 3, 2, 2]
def baseStart_2026783 : Nat := 118140960795 + 2026783 * 2 ^ 59
def prefixEnd_2026783 : Nat := 4983230072969 + 3 ^ 40 * 2026783 * 2
def baseEnd_2026783 : Nat := 1040713861361648935891501

theorem tailTrace_2026783 : CollatzResearch.WordTrace tailWord_2026783 prefixEnd_2026783 1040713861361648935891501 := by
  unfold tailWord_2026783
  simp only [CollatzResearch.WordTrace]
  refine ⟨73922849016318812823341003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49281899344212541882227335 73922849016318812823341003)
  ·
    refine ⟨110884273524478219235011505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73922849016318812823341003 110884273524478219235011505)
    ·
      refine ⟨83163205143358664426258629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110884273524478219235011505 83163205143358664426258629)
      ·
        refine ⟨15593100964379749579923493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83163205143358664426258629 15593100964379749579923493)
        ·
          refine ⟨2923706430821203046235655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15593100964379749579923493 2923706430821203046235655)
          ·
            refine ⟨4385559646231804569353483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923706430821203046235655 4385559646231804569353483)
            ·
              refine ⟨6578339469347706854030225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385559646231804569353483 6578339469347706854030225)
              ·
                refine ⟨4933754602010780140522669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578339469347706854030225 4933754602010780140522669)
                ·
                  refine ⟨1850157975754042552696001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4933754602010780140522669 1850157975754042552696001)
                  ·
                    refine ⟨1387618481815531914522001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1850157975754042552696001 1387618481815531914522001)
                    ·
                      refine ⟨1040713861361648935891501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387618481815531914522001 1040713861361648935891501)
                      ·
                        rfl

theorem cell23_2026783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_2026783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026783 prefixEnd_2026783 := by exact prefixLift 2026783
  have htrace : WordTrace (prefixWord ++ tailWord_2026783) baseStart_2026783 baseEnd_2026783 := by
    simpa [prefixWord, tailWord_2026783, baseEnd_2026783] using wordTrace_append hprefix tailTrace_2026783
  have hstable : (prefixWord ++ tailWord_2026783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026783).length < 2 ^ (prefixWord ++ tailWord_2026783).sum := by decide
  have hdescent : baseEnd_2026783 < baseStart_2026783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026789 : List Nat := [1, 3, 1, 2, 4, 2, 3, 7]
def baseStart_2026789 : Nat := 118140960795 + 2026789 * 2 ^ 59
def prefixEnd_2026789 : Nat := 4983230072969 + 3 ^ 40 * 2026789 * 2
def baseEnd_2026789 : Nat := 38545071935021330089499

theorem tailTrace_2026789 : CollatzResearch.WordTrace tailWord_2026789 prefixEnd_2026789 38545071935021330089499 := by
  unfold tailWord_2026789
  simp only [CollatzResearch.WordTrace]
  refine ⟨73923067854297075848059421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49282045236198050565372947 73923067854297075848059421)
  ·
    refine ⟨27721150445361403443022283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73923067854297075848059421 27721150445361403443022283)
    ·
      refine ⟨41581725668042105164533425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27721150445361403443022283 41581725668042105164533425)
      ·
        refine ⟨31186294251031578873400069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41581725668042105164533425 31186294251031578873400069)
        ·
          refine ⟨5847430172068421038762513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31186294251031578873400069 5847430172068421038762513)
          ·
            refine ⟨4385572629051315779071885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5847430172068421038762513 4385572629051315779071885)
            ·
              refine ⟨1644589735894243417151957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4385572629051315779071885 1644589735894243417151957)
              ·
                refine ⟨38545071935021330089499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1644589735894243417151957 38545071935021330089499)
                ·
                  rfl

theorem cell23_2026789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 7].length) (baseStart_2026789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026789 prefixEnd_2026789 := by exact prefixLift 2026789
  have htrace : WordTrace (prefixWord ++ tailWord_2026789) baseStart_2026789 baseEnd_2026789 := by
    simpa [prefixWord, tailWord_2026789, baseEnd_2026789] using wordTrace_append hprefix tailTrace_2026789
  have hstable : (prefixWord ++ tailWord_2026789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026789).length < 2 ^ (prefixWord ++ tailWord_2026789).sum := by decide
  have hdescent : baseEnd_2026789 < baseStart_2026789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026799 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 3]
def baseStart_2026799 : Nat := 118140960795 + 2026799 * 2 ^ 59
def prefixEnd_2026799 : Nat := 4983230072969 + 3 ^ 40 * 2026799 * 2
def baseEnd_2026799 : Nat := 1040722077052120873291427

theorem tailTrace_2026799 : CollatzResearch.WordTrace tailWord_2026799 prefixEnd_2026799 1040722077052120873291427 := by
  unfold tailWord_2026799
  simp only [CollatzResearch.WordTrace]
  refine ⟨73923432584260847555923451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49282288389507231703948967 73923432584260847555923451)
  ·
    refine ⟨110885148876391271333885177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73923432584260847555923451 110885148876391271333885177)
    ·
      refine ⟨83163861657293453500413883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110885148876391271333885177 83163861657293453500413883)
      ·
        refine ⟨124745792485940180250620825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83163861657293453500413883 124745792485940180250620825)
        ·
          refine ⟨93559344364455135187965619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124745792485940180250620825 93559344364455135187965619)
          ·
            refine ⟨140339016546682702781948429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93559344364455135187965619 140339016546682702781948429)
            ·
              refine ⟨52627131205006013543230661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140339016546682702781948429 52627131205006013543230661)
              ·
                refine ⟨9867587100938627539355749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52627131205006013543230661 9867587100938627539355749)
                ·
                  refine ⟨1850172581425992663629203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9867587100938627539355749 1850172581425992663629203)
                  ·
                    refine ⟨2775258872138988995443805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1850172581425992663629203 2775258872138988995443805)
                    ·
                      refine ⟨1040722077052120873291427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2775258872138988995443805 1040722077052120873291427)
                      ·
                        rfl

theorem cell23_2026799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 1, 3].length) (baseStart_2026799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026799 prefixEnd_2026799 := by exact prefixLift 2026799
  have htrace : WordTrace (prefixWord ++ tailWord_2026799) baseStart_2026799 baseEnd_2026799 := by
    simpa [prefixWord, tailWord_2026799, baseEnd_2026799] using wordTrace_append hprefix tailTrace_2026799
  have hstable : (prefixWord ++ tailWord_2026799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026799).length < 2 ^ (prefixWord ++ tailWord_2026799).sum := by decide
  have hdescent : baseEnd_2026799 < baseStart_2026799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026803 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 1, 2, 3]
def baseStart_2026803 : Nat := 118140960795 + 2026803 * 2 ^ 59
def prefixEnd_2026803 : Nat := 4983230072969 + 3 ^ 40 * 2026803 * 2
def baseEnd_2026803 : Nat := 1040724130974738857641409

theorem tailTrace_2026803 : CollatzResearch.WordTrace tailWord_2026803 prefixEnd_2026803 1040724130974738857641409 := by
  unfold tailWord_2026803
  simp only [CollatzResearch.WordTrace]
  refine ⟨73923578476246356239069063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49282385650830904159379375 73923578476246356239069063)
  ·
    refine ⟨110885367714369534358603595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73923578476246356239069063 110885367714369534358603595)
    ·
      refine ⟨166328051571554301537905393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110885367714369534358603595 166328051571554301537905393)
      ·
        refine ⟨124746038678665726153429045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166328051571554301537905393 124746038678665726153429045)
        ·
          refine ⟨11694941126124911826883973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124746038678665726153429045 11694941126124911826883973)
          ·
            refine ⟨2192801461148420967540745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11694941126124911826883973 2192801461148420967540745)
            ·
              refine ⟨1644601095861315725655559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192801461148420967540745 1644601095861315725655559)
              ·
                refine ⟨2466901643791973588483339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644601095861315725655559 2466901643791973588483339)
                ·
                  refine ⟨3700352465687960382725009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2466901643791973588483339 3700352465687960382725009)
                  ·
                    refine ⟨2775264349265970287043757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3700352465687960382725009 2775264349265970287043757)
                    ·
                      refine ⟨1040724130974738857641409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2775264349265970287043757 1040724130974738857641409)
                      ·
                        rfl

theorem cell23_2026803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 1, 2, 3].length) (baseStart_2026803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026803 prefixEnd_2026803 := by exact prefixLift 2026803
  have htrace : WordTrace (prefixWord ++ tailWord_2026803) baseStart_2026803 baseEnd_2026803 := by
    simpa [prefixWord, tailWord_2026803, baseEnd_2026803] using wordTrace_append hprefix tailTrace_2026803
  have hstable : (prefixWord ++ tailWord_2026803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026803).length < 2 ^ (prefixWord ++ tailWord_2026803).sum := by decide
  have hdescent : baseEnd_2026803 < baseStart_2026803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026806 : List Nat := [5, 1, 2, 3, 1, 1, 10]
def baseStart_2026806 : Nat := 118140960795 + 2026806 * 2 ^ 59
def prefixEnd_2026806 : Nat := 4983230072969 + 3 ^ 40 * 2026806 * 2
def baseEnd_2026806 : Nat := 12848465079218547480295

theorem tailTrace_2026806 : CollatzResearch.WordTrace tailWord_2026806 prefixEnd_2026806 12848465079218547480295 := by
  unfold tailWord_2026806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4620230493452217984464267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49282458596823658500952181 4620230493452217984464267)
  ·
    refine ⟨6930345740178326976696401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4620230493452217984464267 6930345740178326976696401)
    ·
      refine ⟨5197759305133745232522301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6930345740178326976696401 5197759305133745232522301)
      ·
        refine ⟨1949159739425154462195863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5197759305133745232522301 1949159739425154462195863)
        ·
          refine ⟨2923739609137731693293795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1949159739425154462195863 2923739609137731693293795)
          ·
            refine ⟨4385609413706597539940693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923739609137731693293795 4385609413706597539940693)
            ·
              refine ⟨12848465079218547480295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4385609413706597539940693 12848465079218547480295)
              ·
                rfl

theorem cell23_2026806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 10].length) (baseStart_2026806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026806 prefixEnd_2026806 := by exact prefixLift 2026806
  have htrace : WordTrace (prefixWord ++ tailWord_2026806) baseStart_2026806 baseEnd_2026806 := by
    simpa [prefixWord, tailWord_2026806, baseEnd_2026806] using wordTrace_append hprefix tailTrace_2026806
  have hstable : (prefixWord ++ tailWord_2026806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026806).length < 2 ^ (prefixWord ++ tailWord_2026806).sum := by decide
  have hdescent : baseEnd_2026806 < baseStart_2026806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026832 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 2, 6]
def baseStart_2026832 : Nat := 118140960795 + 2026832 * 2 ^ 59
def prefixEnd_2026832 : Nat := 4983230072969 + 3 ^ 40 * 2026832 * 2
def baseEnd_2026832 : Nat := 346913007304573081392925

theorem tailTrace_2026832 : CollatzResearch.WordTrace tailWord_2026832 prefixEnd_2026832 346913007304573081392925 := by
  unfold tailWord_2026832
  simp only [CollatzResearch.WordTrace]
  refine ⟨36962318096570647095937375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49283090795427529461249833 36962318096570647095937375)
  ·
    refine ⟨55443477144855970643906063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36962318096570647095937375 55443477144855970643906063)
    ·
      refine ⟨83165215717283955965859095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55443477144855970643906063 83165215717283955965859095)
      ·
        refine ⟨124747823575925933948788643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83165215717283955965859095 124747823575925933948788643)
        ·
          refine ⟨187121735363888900923182965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124747823575925933948788643 187121735363888900923182965)
          ·
            refine ⟨17542662690364584461548403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187121735363888900923182965 17542662690364584461548403)
            ·
              refine ⟨26313994035546876692322605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17542662690364584461548403 26313994035546876692322605)
              ·
                refine ⟨9867747763330078759620977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26313994035546876692322605 9867747763330078759620977)
                ·
                  refine ⟨7400810822497559069715733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9867747763330078759620977 7400810822497559069715733)
                  ·
                    refine ⟨346913007304573081392925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7400810822497559069715733 346913007304573081392925)
                    ·
                      rfl

theorem cell23_2026832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_2026832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026832 prefixEnd_2026832 := by exact prefixLift 2026832
  have htrace : WordTrace (prefixWord ++ tailWord_2026832) baseStart_2026832 baseEnd_2026832 := by
    simpa [prefixWord, tailWord_2026832, baseEnd_2026832] using wordTrace_append hprefix tailTrace_2026832
  have hstable : (prefixWord ++ tailWord_2026832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026832).length < 2 ^ (prefixWord ++ tailWord_2026832).sum := by decide
  have hdescent : baseEnd_2026832 < baseStart_2026832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026833 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 2, 1, 3]
def baseStart_2026833 : Nat := 118140960795 + 2026833 * 2 ^ 59
def prefixEnd_2026833 : Nat := 4983230072969 + 3 ^ 40 * 2026833 * 2
def baseEnd_2026833 : Nat := 1040739535394373740266271

theorem tailTrace_2026833 : CollatzResearch.WordTrace tailWord_2026833 prefixEnd_2026833 1040739535394373740266271 := by
  unfold tailWord_2026833
  simp only [CollatzResearch.WordTrace]
  refine ⟨73924672666137671362661153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49283115110758447575107435 73924672666137671362661153)
  ·
    refine ⟨55443504499603253521995865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73924672666137671362661153 55443504499603253521995865)
    ·
      refine ⟨41582628374702440141496899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55443504499603253521995865 41582628374702440141496899)
      ·
        refine ⟨62373942562053660212245349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41582628374702440141496899 62373942562053660212245349)
        ·
          refine ⟨11695114230385061289796003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62373942562053660212245349 11695114230385061289796003)
          ·
            refine ⟨17542671345577591934694005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695114230385061289796003 17542671345577591934694005)
            ·
              refine ⟨1644625438647899243877563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17542671345577591934694005 1644625438647899243877563)
              ·
                refine ⟨2466938157971848865816345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644625438647899243877563 2466938157971848865816345)
                ·
                  refine ⟨1850203618478886649362259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2466938157971848865816345 1850203618478886649362259)
                  ·
                    refine ⟨2775305427718329974043389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1850203618478886649362259 2775305427718329974043389)
                    ·
                      refine ⟨1040739535394373740266271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2775305427718329974043389 1040739535394373740266271)
                      ·
                        rfl

theorem cell23_2026833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_2026833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026833 prefixEnd_2026833 := by exact prefixLift 2026833
  have htrace : WordTrace (prefixWord ++ tailWord_2026833) baseStart_2026833 baseEnd_2026833 := by
    simpa [prefixWord, tailWord_2026833, baseEnd_2026833] using wordTrace_append hprefix tailTrace_2026833
  have hstable : (prefixWord ++ tailWord_2026833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026833).length < 2 ^ (prefixWord ++ tailWord_2026833).sum := by decide
  have hdescent : baseEnd_2026833 < baseStart_2026833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026919 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_2026919 : Nat := 118140960795 + 2026919 * 2 ^ 59
def prefixEnd_2026919 : Nat := 4983230072969 + 3 ^ 40 * 2026919 * 2
def baseEnd_2026919 : Nat := 1040783694730660403790875

theorem tailTrace_2026919 : CollatzResearch.WordTrace tailWord_2026919 prefixEnd_2026919 1040783694730660403790875 := by
  unfold tailWord_2026919
  simp only [CollatzResearch.WordTrace]
  refine ⟨73927809343826108050291811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49285206229217405366861207 73927809343826108050291811)
  ·
    refine ⟨110891714015739162075437717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73927809343826108050291811 110891714015739162075437717)
    ·
      refine ⟨5198049094487773222286143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110891714015739162075437717 5198049094487773222286143)
      ·
        refine ⟨7797073641731659833429215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198049094487773222286143 7797073641731659833429215)
        ·
          refine ⟨11695610462597489750143823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797073641731659833429215 11695610462597489750143823)
          ·
            refine ⟨17543415693896234625215735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695610462597489750143823 17543415693896234625215735)
            ·
              refine ⟨26315123540844351937823603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17543415693896234625215735 26315123540844351937823603)
              ·
                refine ⟨39472685311266527906735405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26315123540844351937823603 39472685311266527906735405)
                ·
                  refine ⟨14802256991724947965025777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39472685311266527906735405 14802256991724947965025777)
                  ·
                    refine ⟨11101692743793710973769333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14802256991724947965025777 11101692743793710973769333)
                    ·
                      refine ⟨1040783694730660403790875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11101692743793710973769333 1040783694730660403790875)
                      ·
                        rfl

theorem cell23_2026919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_2026919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026919 prefixEnd_2026919 := by exact prefixLift 2026919
  have htrace : WordTrace (prefixWord ++ tailWord_2026919) baseStart_2026919 baseEnd_2026919 := by
    simpa [prefixWord, tailWord_2026919, baseEnd_2026919] using wordTrace_append hprefix tailTrace_2026919
  have hstable : (prefixWord ++ tailWord_2026919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026919).length < 2 ^ (prefixWord ++ tailWord_2026919).sum := by decide
  have hdescent : baseEnd_2026919 < baseStart_2026919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026956 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_2026956 : Nat := 118140960795 + 2026956 * 2 ^ 59
def prefixEnd_2026956 : Nat := 4983230072969 + 3 ^ 40 * 2026956 * 2
def baseEnd_2026956 : Nat := 346934231171625586342735

theorem tailTrace_2026956 : CollatzResearch.WordTrace tailWord_2026956 prefixEnd_2026956 346934231171625586342735 := by
  unfold tailWord_2026956
  simp only [CollatzResearch.WordTrace]
  refine ⟨36964579422346031684694361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49286105896461375579592481 36964579422346031684694361)
  ·
    refine ⟨27723434566759523763520771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36964579422346031684694361 27723434566759523763520771)
    ·
      refine ⟨41585151850139285645281157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27723434566759523763520771 41585151850139285645281157)
      ·
        refine ⟨7797215971901116058490217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41585151850139285645281157 7797215971901116058490217)
        ·
          refine ⟨5847911978925837043867663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7797215971901116058490217 5847911978925837043867663)
          ·
            refine ⟨8771867968388755565801495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5847911978925837043867663 8771867968388755565801495)
            ·
              refine ⟨13157801952583133348702243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8771867968388755565801495 13157801952583133348702243)
              ·
                refine ⟨19736702928874700023053365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157801952583133348702243 19736702928874700023053365)
                ·
                  refine ⟨1850315899582003127161253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19736702928874700023053365 1850315899582003127161253)
                  ·
                    refine ⟨346934231171625586342735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1850315899582003127161253 346934231171625586342735)
                    ·
                      rfl

theorem cell23_2026956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_2026956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026956 prefixEnd_2026956 := by exact prefixLift 2026956
  have htrace : WordTrace (prefixWord ++ tailWord_2026956) baseStart_2026956 baseEnd_2026956 := by
    simpa [prefixWord, tailWord_2026956, baseEnd_2026956] using wordTrace_append hprefix tailTrace_2026956
  have hstable : (prefixWord ++ tailWord_2026956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026956).length < 2 ^ (prefixWord ++ tailWord_2026956).sum := by decide
  have hdescent : baseEnd_2026956 < baseStart_2026956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026986 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 8]
def baseStart_2026986 : Nat := 118140960795 + 2026986 * 2 ^ 59
def prefixEnd_2026986 : Nat := 4983230072969 + 3 ^ 40 * 2026986 * 2
def baseEnd_2026986 : Nat := 115646455326056849072563

theorem tailTrace_2026986 : CollatzResearch.WordTrace tailWord_2026986 prefixEnd_2026986 115646455326056849072563 := by
  unfold tailWord_2026986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482563258645844623245203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49286835356388918995320541 18482563258645844623245203)
  ·
    refine ⟨27723844887968766934867805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18482563258645844623245203 27723844887968766934867805)
    ·
      refine ⟨10396441832988287600575427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27723844887968766934867805 10396441832988287600575427)
      ·
        refine ⟨15594662749482431400863141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10396441832988287600575427 15594662749482431400863141)
        ·
          refine ⟨2923999265527955887661839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15594662749482431400863141 2923999265527955887661839)
          ·
            refine ⟨4385998898291933831492759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2923999265527955887661839 4385998898291933831492759)
            ·
              refine ⟨6578998347437900747239139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4385998898291933831492759 6578998347437900747239139)
              ·
                refine ⟨9868497521156851120858709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578998347437900747239139 9868497521156851120858709)
                ·
                  refine ⟨115646455326056849072563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9868497521156851120858709 115646455326056849072563)
                  ·
                    rfl

theorem cell23_2026986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_2026986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026986 prefixEnd_2026986 := by exact prefixLift 2026986
  have htrace : WordTrace (prefixWord ++ tailWord_2026986) baseStart_2026986 baseEnd_2026986 := by
    simpa [prefixWord, tailWord_2026986, baseEnd_2026986] using wordTrace_append hprefix tailTrace_2026986
  have hstable : (prefixWord ++ tailWord_2026986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026986).length < 2 ^ (prefixWord ++ tailWord_2026986).sum := by decide
  have hdescent : baseEnd_2026986 < baseStart_2026986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2026999 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 3, 5]
def baseStart_2026999 : Nat := 118140960795 + 2026999 * 2 ^ 59
def prefixEnd_2026999 : Nat := 4983230072969 + 3 ^ 40 * 2026999 * 2
def baseEnd_2026999 : Nat := 346941591061006696930169

theorem tailTrace_2026999 : CollatzResearch.WordTrace tailWord_2026999 prefixEnd_2026999 346941591061006696930169 := by
  unfold tailWord_2026999
  simp only [CollatzResearch.WordTrace]
  refine ⟨73930727183536281713204051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49287151455690854475469367 73930727183536281713204051)
  ·
    refine ⟨110896090775304422569806077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73930727183536281713204051 110896090775304422569806077)
    ·
      refine ⟨41586034040739158463677279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110896090775304422569806077 41586034040739158463677279)
      ·
        refine ⟨62379051061108737695515919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41586034040739158463677279 62379051061108737695515919)
        ·
          refine ⟨93568576591663106543273879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62379051061108737695515919 93568576591663106543273879)
          ·
            refine ⟨140352864887494659814910819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93568576591663106543273879 140352864887494659814910819)
            ·
              refine ⟨210529297331241989722366229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140352864887494659814910819 210529297331241989722366229)
              ·
                refine ⟨9868560812401968268235917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 210529297331241989722366229 9868560812401968268235917)
                ·
                  refine ⟨3700710304650738100588469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9868560812401968268235917 3700710304650738100588469)
                  ·
                    refine ⟨346941591061006696930169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3700710304650738100588469 346941591061006696930169)
                    ·
                      rfl

theorem cell23_2026999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_2026999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2026999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2026999 prefixEnd_2026999 := by exact prefixLift 2026999
  have htrace : WordTrace (prefixWord ++ tailWord_2026999) baseStart_2026999 baseEnd_2026999 := by
    simpa [prefixWord, tailWord_2026999, baseEnd_2026999] using wordTrace_append hprefix tailTrace_2026999
  have hstable : (prefixWord ++ tailWord_2026999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2026999).length < 2 ^ (prefixWord ++ tailWord_2026999).sum := by decide
  have hdescent : baseEnd_2026999 < baseStart_2026999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2026999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027016 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 1, 5]
def baseStart_2027016 : Nat := 118140960795 + 2027016 * 2 ^ 59
def prefixEnd_2027016 : Nat := 4983230072969 + 3 ^ 40 * 2027016 * 2
def baseEnd_2027016 : Nat := 346944500784715508092643

theorem tailTrace_2027016 : CollatzResearch.WordTrace tailWord_2027016 prefixEnd_2027016 346944500784715508092643 := by
  unfold tailWord_2027016
  simp only [CollatzResearch.WordTrace]
  refine ⟨36965673612237346808286451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49287564816316462411048601 36965673612237346808286451)
  ·
    refine ⟨55448510418356020212429677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36965673612237346808286451 55448510418356020212429677)
    ·
      refine ⟨20793191406883507579661129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55448510418356020212429677 20793191406883507579661129)
      ·
        refine ⟨15594893555162630684745847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20793191406883507579661129 15594893555162630684745847)
        ·
          refine ⟨23392340332743946027118771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15594893555162630684745847 23392340332743946027118771)
          ·
            refine ⟨35088510499115919040678157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23392340332743946027118771 35088510499115919040678157)
            ·
              refine ⟨13158191437168469640254309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35088510499115919040678157 13158191437168469640254309)
              ·
                refine ⟨2467160894469088057547683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13158191437168469640254309 2467160894469088057547683)
                ·
                  refine ⟨3700741341703632086321525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467160894469088057547683 3700741341703632086321525)
                  ·
                    refine ⟨346944500784715508092643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3700741341703632086321525 346944500784715508092643)
                    ·
                      rfl

theorem cell23_2027016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_2027016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027016 prefixEnd_2027016 := by exact prefixLift 2027016
  have htrace : WordTrace (prefixWord ++ tailWord_2027016) baseStart_2027016 baseEnd_2027016 := by
    simpa [prefixWord, tailWord_2027016, baseEnd_2027016] using wordTrace_append hprefix tailTrace_2027016
  have hstable : (prefixWord ++ tailWord_2027016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027016).length < 2 ^ (prefixWord ++ tailWord_2027016).sum := by decide
  have hdescent : baseEnd_2027016 < baseStart_2027016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027040 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2027040 : Nat := 118140960795 + 2027040 * 2 ^ 59
def prefixEnd_2027040 : Nat := 4983230072969 + 3 ^ 40 * 2027040 * 2
def baseEnd_2027040 : Nat := 1040845825889854430377819

theorem tailTrace_2027040 : CollatzResearch.WordTrace tailWord_2027040 prefixEnd_2027040 1040845825889854430377819 := by
  unfold tailWord_2027040
  simp only [CollatzResearch.WordTrace]
  refine ⟨36966111288193872857723287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49288148384258497143631049 36966111288193872857723287)
  ·
    refine ⟨55449166932290809286584931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36966111288193872857723287 55449166932290809286584931)
    ·
      refine ⟨83173750398436213929877397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55449166932290809286584931 83173750398436213929877397)
      ·
        refine ⟨3898769549926697527963003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83173750398436213929877397 3898769549926697527963003)
        ·
          refine ⟨5848154324890046291944505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3898769549926697527963003 5848154324890046291944505)
          ·
            refine ⟨4386115743667534718958379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5848154324890046291944505 4386115743667534718958379)
            ·
              refine ⟨6579173615501302078437569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386115743667534718958379 6579173615501302078437569)
              ·
                refine ⟨4934380211625976558828177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6579173615501302078437569 4934380211625976558828177)
                ·
                  refine ⟨3700785158719482419121133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4934380211625976558828177 3700785158719482419121133)
                  ·
                    refine ⟨1387794434519805907170425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700785158719482419121133 1387794434519805907170425)
                    ·
                      refine ⟨1040845825889854430377819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387794434519805907170425 1040845825889854430377819)
                      ·
                        rfl

theorem cell23_2027040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2027040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027040 prefixEnd_2027040 := by exact prefixLift 2027040
  have htrace : WordTrace (prefixWord ++ tailWord_2027040) baseStart_2027040 baseEnd_2027040 := by
    simpa [prefixWord, tailWord_2027040, baseEnd_2027040] using wordTrace_append hprefix tailTrace_2027040
  have hstable : (prefixWord ++ tailWord_2027040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027040).length < 2 ^ (prefixWord ++ tailWord_2027040).sum := by decide
  have hdescent : baseEnd_2027040 < baseStart_2027040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027056 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3]
def baseStart_2027056 : Nat := 118140960795 + 2027056 * 2 ^ 59
def prefixEnd_2027056 : Nat := 4983230072969 + 3 ^ 40 * 2027056 * 2
def baseEnd_2027056 : Nat := 1040854041580326367777745

theorem tailTrace_2027056 : CollatzResearch.WordTrace tailWord_2027056 prefixEnd_2027056 1040854041580326367777745 := by
  unfold tailWord_2027056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36966403072164890224014511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49288537429553186965352681 36966403072164890224014511)
  ·
    refine ⟨55449604608247335336021767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36966403072164890224014511 55449604608247335336021767)
    ·
      refine ⟨83174406912371003004032651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55449604608247335336021767 83174406912371003004032651)
      ·
        refine ⟨124761610368556504506048977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83174406912371003004032651 124761610368556504506048977)
        ·
          refine ⟨93571207776417378379536733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124761610368556504506048977 93571207776417378379536733)
          ·
            refine ⟨35089202916156516892326275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93571207776417378379536733 35089202916156516892326275)
            ·
              refine ⟨52633804374234775338489413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35089202916156516892326275 52633804374234775338489413)
              ·
                refine ⟨9868838320169020375966765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52633804374234775338489413 9868838320169020375966765)
                ·
                  refine ⟨3700814370063382640987537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9868838320169020375966765 3700814370063382640987537)
                  ·
                    refine ⟨2775610777547536980740653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3700814370063382640987537 2775610777547536980740653)
                    ·
                      refine ⟨1040854041580326367777745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2775610777547536980740653 1040854041580326367777745)
                      ·
                        rfl

theorem cell23_2027056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_2027056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027056 prefixEnd_2027056 := by exact prefixLift 2027056
  have htrace : WordTrace (prefixWord ++ tailWord_2027056) baseStart_2027056 baseEnd_2027056 := by
    simpa [prefixWord, tailWord_2027056, baseEnd_2027056] using wordTrace_append hprefix tailTrace_2027056
  have hstable : (prefixWord ++ tailWord_2027056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027056).length < 2 ^ (prefixWord ++ tailWord_2027056).sum := by decide
  have hdescent : baseEnd_2027056 < baseStart_2027056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027059 : List Nat := [1, 1, 1, 2, 4, 3, 1, 10]
def baseStart_2027059 : Nat := 118140960795 + 2027059 * 2 ^ 59
def prefixEnd_2027059 : Nat := 4983230072969 + 3 ^ 40 * 2027059 * 2
def baseEnd_2027059 : Nat := 38550206741566290964453

theorem tailTrace_2027059 : CollatzResearch.WordTrace tailWord_2027059 prefixEnd_2027059 38550206741566290964453 := by
  unfold tailWord_2027059
  simp only [CollatzResearch.WordTrace]
  refine ⟨73932915563318911960388231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49288610375545941306925487 73932915563318911960388231)
  ·
    refine ⟨110899373344978367940582347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73932915563318911960388231 110899373344978367940582347)
    ·
      refine ⟨166349060017467551910873521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110899373344978367940582347 166349060017467551910873521)
      ·
        refine ⟨124761795013100663933155141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166349060017467551910873521 124761795013100663933155141)
        ·
          refine ⟨23392836564956374487466589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124761795013100663933155141 23392836564956374487466589)
          ·
            refine ⟨8772313711858640432799971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23392836564956374487466589 8772313711858640432799971)
            ·
              refine ⟨13158470567787960649199957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8772313711858640432799971 13158470567787960649199957)
              ·
                refine ⟨38550206741566290964453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13158470567787960649199957 38550206741566290964453)
                ·
                  rfl

theorem cell23_2027059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 10].length) (baseStart_2027059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027059 prefixEnd_2027059 := by exact prefixLift 2027059
  have htrace : WordTrace (prefixWord ++ tailWord_2027059) baseStart_2027059 baseEnd_2027059 := by
    simpa [prefixWord, tailWord_2027059, baseEnd_2027059] using wordTrace_append hprefix tailTrace_2027059
  have hstable : (prefixWord ++ tailWord_2027059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027059).length < 2 ^ (prefixWord ++ tailWord_2027059).sum := by decide
  have hdescent : baseEnd_2027059 < baseStart_2027059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027063 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 2, 4]
def baseStart_2027063 : Nat := 118140960795 + 2027063 * 2 ^ 59
def prefixEnd_2027063 : Nat := 4983230072969 + 3 ^ 40 * 2027063 * 2
def baseEnd_2027063 : Nat := 346952545314969280130071

theorem tailTrace_2027063 : CollatzResearch.WordTrace tailWord_2027063 prefixEnd_2027063 346952545314969280130071 := by
  unfold tailWord_2027063
  simp only [CollatzResearch.WordTrace]
  refine ⟨73933061455304420643533843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49288707636869613762355895 73933061455304420643533843)
  ·
    refine ⟨110899592182956630965300765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73933061455304420643533843 110899592182956630965300765)
    ·
      refine ⟨41587347068608736611987787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110899592182956630965300765 41587347068608736611987787)
      ·
        refine ⟨62381020602913104917981681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41587347068608736611987787 62381020602913104917981681)
        ·
          refine ⟨46785765452184828688486261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62381020602913104917981681 46785765452184828688486261)
          ·
            refine ⟨4386165511142327689545587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46785765452184828688486261 4386165511142327689545587)
            ·
              refine ⟨6579248266713491534318381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386165511142327689545587 6579248266713491534318381)
              ·
                refine ⟨2467218100017559325369393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6579248266713491534318381 2467218100017559325369393)
                ·
                  refine ⟨1850413575013169494027045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2467218100017559325369393 1850413575013169494027045)
                  ·
                    refine ⟨346952545314969280130071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1850413575013169494027045 346952545314969280130071)
                    ·
                      rfl

theorem cell23_2027063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_2027063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027063 prefixEnd_2027063 := by exact prefixLift 2027063
  have htrace : WordTrace (prefixWord ++ tailWord_2027063) baseStart_2027063 baseEnd_2027063 := by
    simpa [prefixWord, tailWord_2027063, baseEnd_2027063] using wordTrace_append hprefix tailTrace_2027063
  have hstable : (prefixWord ++ tailWord_2027063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027063).length < 2 ^ (prefixWord ++ tailWord_2027063).sum := by decide
  have hdescent : baseEnd_2027063 < baseStart_2027063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027066 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_2027066 : Nat := 118140960795 + 2027066 * 2 ^ 59
def prefixEnd_2027066 : Nat := 4983230072969 + 3 ^ 40 * 2027066 * 2
def baseEnd_2027066 : Nat := 1040859176386871328652699

theorem tailTrace_2027066 : CollatzResearch.WordTrace tailWord_2027066 prefixEnd_2027066 1040859176386871328652699 := by
  unfold tailWord_2027066
  simp only [CollatzResearch.WordTrace]
  refine ⟨18483292718573388038973263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49288780582862368103928701 18483292718573388038973263)
  ·
    refine ⟨27724939077860082058459895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18483292718573388038973263 27724939077860082058459895)
    ·
      refine ⟨41587408616790123087689843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27724939077860082058459895 41587408616790123087689843)
      ·
        refine ⟨62381112925185184631534765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41587408616790123087689843 62381112925185184631534765)
        ·
          refine ⟨23392917346944444236825537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62381112925185184631534765 23392917346944444236825537)
          ·
            refine ⟨17544688010208333177619153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23392917346944444236825537 17544688010208333177619153)
            ·
              refine ⟨13158516007656249883214365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17544688010208333177619153 13158516007656249883214365)
              ·
                refine ⟨4934443502871093706205387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13158516007656249883214365 4934443502871093706205387)
                ·
                  refine ⟨7401665254306640559308081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4934443502871093706205387 7401665254306640559308081)
                  ·
                    refine ⟨5551248940729980419481061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7401665254306640559308081 5551248940729980419481061)
                    ·
                      refine ⟨1040859176386871328652699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5551248940729980419481061 1040859176386871328652699)
                      ·
                        rfl

theorem cell23_2027066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_2027066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027066 prefixEnd_2027066 := by exact prefixLift 2027066
  have htrace : WordTrace (prefixWord ++ tailWord_2027066) baseStart_2027066 baseEnd_2027066 := by
    simpa [prefixWord, tailWord_2027066, baseEnd_2027066] using wordTrace_append hprefix tailTrace_2027066
  have hstable : (prefixWord ++ tailWord_2027066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027066).length < 2 ^ (prefixWord ++ tailWord_2027066).sum := by decide
  have hdescent : baseEnd_2027066 < baseStart_2027066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027073 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2027073 : Nat := 118140960795 + 2027073 * 2 ^ 59
def prefixEnd_2027073 : Nat := 4983230072969 + 3 ^ 40 * 2027073 * 2
def baseEnd_2027073 : Nat := 1040862770751452801265167

theorem tailTrace_2027073 : CollatzResearch.WordTrace tailWord_2027073 prefixEnd_2027073 1040862770751452801265167 := by
  unfold tailWord_2027073
  simp only [CollatzResearch.WordTrace]
  refine ⟨73933426185268192351397873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49288950790178794900931915 73933426185268192351397873)
  ·
    refine ⟨55450069638951144263548405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73933426185268192351397873 55450069638951144263548405)
    ·
      refine ⟨5198444028651669774707663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55450069638951144263548405 5198444028651669774707663)
      ·
        refine ⟨7797666042977504662061495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198444028651669774707663 7797666042977504662061495)
        ·
          refine ⟨11696499064466256993092243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7797666042977504662061495 11696499064466256993092243)
          ·
            refine ⟨17544748596699385489638365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11696499064466256993092243 17544748596699385489638365)
            ·
              refine ⟨6579280723762269558614387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17544748596699385489638365 6579280723762269558614387)
              ·
                refine ⟨9868921085643404337921581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6579280723762269558614387 9868921085643404337921581)
                ·
                  refine ⟨3700845407116276626720593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9868921085643404337921581 3700845407116276626720593)
                  ·
                    refine ⟨2775634055337207470040445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3700845407116276626720593 2775634055337207470040445)
                    ·
                      refine ⟨1040862770751452801265167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2775634055337207470040445 1040862770751452801265167)
                      ·
                        rfl

theorem cell23_2027073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2027073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027073 prefixEnd_2027073 := by exact prefixLift 2027073
  have htrace : WordTrace (prefixWord ++ tailWord_2027073) baseStart_2027073 baseEnd_2027073 := by
    simpa [prefixWord, tailWord_2027073, baseEnd_2027073] using wordTrace_append hprefix tailTrace_2027073
  have hstable : (prefixWord ++ tailWord_2027073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027073).length < 2 ^ (prefixWord ++ tailWord_2027073).sum := by decide
  have hdescent : baseEnd_2027073 < baseStart_2027073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027113 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 3, 3, 2]
def baseStart_2027113 : Nat := 118140960795 + 2027113 * 2 ^ 59
def prefixEnd_2027113 : Nat := 4983230072969 + 3 ^ 40 * 2027113 * 2
def baseEnd_2027113 : Nat := 1040883309977632644764983

theorem tailTrace_2027113 : CollatzResearch.WordTrace tailWord_2027113 prefixEnd_2027113 1040883309977632644764983 := by
  unfold tailWord_2027113
  simp only [CollatzResearch.WordTrace]
  refine ⟨73934885105123279182853993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49289923403415519455235995 73934885105123279182853993)
  ·
    refine ⟨55451163828842459387140495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73934885105123279182853993 55451163828842459387140495)
    ·
      refine ⟨83176745743263689080710743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55451163828842459387140495 83176745743263689080710743)
      ·
        refine ⟨124765118614895533621066115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83176745743263689080710743 124765118614895533621066115)
        ·
          refine ⟨187147677922343300431599173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124765118614895533621066115 187147677922343300431599173)
          ·
            refine ⟨35090189610439368830924845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187147677922343300431599173 35090189610439368830924845)
            ·
              refine ⟨13158821103914763311596817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35090189610439368830924845 13158821103914763311596817)
              ·
                refine ⟨9869115827936072483697613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13158821103914763311596817 9869115827936072483697613)
                ·
                  refine ⟨3700918435476027181386605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9869115827936072483697613 3700918435476027181386605)
                  ·
                    refine ⟨1387844413303510193019977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3700918435476027181386605 1387844413303510193019977)
                    ·
                      refine ⟨1040883309977632644764983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387844413303510193019977 1040883309977632644764983)
                      ·
                        rfl

theorem cell23_2027113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 3, 2].length) (baseStart_2027113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027113 prefixEnd_2027113 := by exact prefixLift 2027113
  have htrace : WordTrace (prefixWord ++ tailWord_2027113) baseStart_2027113 baseEnd_2027113 := by
    simpa [prefixWord, tailWord_2027113, baseEnd_2027113] using wordTrace_append hprefix tailTrace_2027113
  have hstable : (prefixWord ++ tailWord_2027113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027113).length < 2 ^ (prefixWord ++ tailWord_2027113).sum := by decide
  have hdescent : baseEnd_2027113 < baseStart_2027113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027120 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 2, 1, 3]
def baseStart_2027120 : Nat := 118140960795 + 2027120 * 2 ^ 59
def prefixEnd_2027120 : Nat := 4983230072969 + 3 ^ 40 * 2027120 * 2
def baseEnd_2027120 : Nat := 1040886904342214117377451

theorem tailTrace_2027120 : CollatzResearch.WordTrace tailWord_2027120 prefixEnd_2027120 1040886904342214117377451 := by
  unfold tailWord_2027120
  simp only [CollatzResearch.WordTrace]
  refine ⟨36967570208048959689179407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49290093610731946252239209 36967570208048959689179407)
  ·
    refine ⟨55451355312073439533769111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36967570208048959689179407 55451355312073439533769111)
    ·
      refine ⟨83177032968110159300653667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55451355312073439533769111 83177032968110159300653667)
      ·
        refine ⟨124765549452165238950980501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83177032968110159300653667 124765549452165238950980501)
        ·
          refine ⟨5848385130570245575827211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124765549452165238950980501 5848385130570245575827211)
          ·
            refine ⟨8772577695855368363740817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5848385130570245575827211 8772577695855368363740817)
            ·
              refine ⟨6579433271891526272805613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8772577695855368363740817 6579433271891526272805613)
              ·
                refine ⟨2467287476959322352302105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6579433271891526272805613 2467287476959322352302105)
                ·
                  refine ⟨1850465607719491764226579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2467287476959322352302105 1850465607719491764226579)
                  ·
                    refine ⟨2775698411579237646339869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1850465607719491764226579 2775698411579237646339869)
                    ·
                      refine ⟨1040886904342214117377451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2775698411579237646339869 1040886904342214117377451)
                      ·
                        rfl

theorem cell23_2027120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 1, 3].length) (baseStart_2027120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027120 prefixEnd_2027120 := by exact prefixLift 2027120
  have htrace : WordTrace (prefixWord ++ tailWord_2027120) baseStart_2027120 baseEnd_2027120 := by
    simpa [prefixWord, tailWord_2027120, baseEnd_2027120] using wordTrace_append hprefix tailTrace_2027120
  have hstable : (prefixWord ++ tailWord_2027120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027120).length < 2 ^ (prefixWord ++ tailWord_2027120).sum := by decide
  have hdescent : baseEnd_2027120 < baseStart_2027120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027154 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_2027154 : Nat := 118140960795 + 2027154 * 2 ^ 59
def prefixEnd_2027154 : Nat := 4983230072969 + 3 ^ 40 * 2027154 * 2
def baseEnd_2027154 : Nat := 1040904362684466984352295

theorem tailTrace_2027154 : CollatzResearch.WordTrace tailWord_2027154 prefixEnd_2027154 1040904362684466984352295 := by
  unfold tailWord_2027154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484095124493685796274129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49290920331983162123397677 18484095124493685796274129)
  ·
    refine ⟨13863071343370264347205597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18484095124493685796274129 13863071343370264347205597)
    ·
      refine ⟨5198651753763849130202099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13863071343370264347205597 5198651753763849130202099)
      ·
        refine ⟨7797977630645773695303149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5198651753763849130202099 7797977630645773695303149)
        ·
          refine ⟨2924241611492165135738681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7797977630645773695303149 2924241611492165135738681)
          ·
            refine ⟨2193181208619123851804011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924241611492165135738681 2193181208619123851804011)
            ·
              refine ⟨3289771812928685777706017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2193181208619123851804011 3289771812928685777706017)
              ·
                refine ⟨2467328859696514333279513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3289771812928685777706017 2467328859696514333279513)
                ·
                  refine ⟨1850496644772385749959635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2467328859696514333279513 1850496644772385749959635)
                  ·
                    refine ⟨2775744967158578624939453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1850496644772385749959635 2775744967158578624939453)
                    ·
                      refine ⟨1040904362684466984352295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2775744967158578624939453 1040904362684466984352295)
                      ·
                        rfl

theorem cell23_2027154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_2027154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027154 prefixEnd_2027154 := by exact prefixLift 2027154
  have htrace : WordTrace (prefixWord ++ tailWord_2027154) baseStart_2027154 baseEnd_2027154 := by
    simpa [prefixWord, tailWord_2027154, baseEnd_2027154] using wordTrace_append hprefix tailTrace_2027154
  have hstable : (prefixWord ++ tailWord_2027154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027154).length < 2 ^ (prefixWord ++ tailWord_2027154).sum := by decide
  have hdescent : baseEnd_2027154 < baseStart_2027154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027216 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_2027216 : Nat := 118140960795 + 2027216 * 2 ^ 59
def prefixEnd_2027216 : Nat := 4983230072969 + 3 ^ 40 * 2027216 * 2
def baseEnd_2027216 : Nat := 1040936198485045741777009

theorem tailTrace_2027216 : CollatzResearch.WordTrace tailWord_2027216 prefixEnd_2027216 1040936198485045741777009 := by
  unfold tailWord_2027216
  simp only [CollatzResearch.WordTrace]
  refine ⟨36969320911875063886926751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49292427882500085182569001 36969320911875063886926751)
  ·
    refine ⟨55453981367812595830390127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36969320911875063886926751 55453981367812595830390127)
    ·
      refine ⟨83180972051718893745585191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55453981367812595830390127 83180972051718893745585191)
      ·
        refine ⟨124771458077578340618377787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83180972051718893745585191 124771458077578340618377787)
        ·
          refine ⟨187157187116367510927566681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124771458077578340618377787 187157187116367510927566681)
          ·
            refine ⟨140367890337275633195675011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187157187116367510927566681 140367890337275633195675011)
            ·
              refine ⟨210551835505913449793512517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140367890337275633195675011 210551835505913449793512517)
              ·
                refine ⟨39478469157358771836283597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210551835505913449793512517 39478469157358771836283597)
                ·
                  refine ⟨14804425934009539438606349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39478469157358771836283597 14804425934009539438606349)
                  ·
                    refine ⟨5551659725253577289477381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14804425934009539438606349 5551659725253577289477381)
                    ·
                      refine ⟨1040936198485045741777009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5551659725253577289477381 1040936198485045741777009)
                      ·
                        rfl

theorem cell23_2027216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_2027216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027216 prefixEnd_2027216 := by exact prefixLift 2027216
  have htrace : WordTrace (prefixWord ++ tailWord_2027216) baseStart_2027216 baseEnd_2027216 := by
    simpa [prefixWord, tailWord_2027216, baseEnd_2027216] using wordTrace_append hprefix tailTrace_2027216
  have hstable : (prefixWord ++ tailWord_2027216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027216).length < 2 ^ (prefixWord ++ tailWord_2027216).sum := by decide
  have hdescent : baseEnd_2027216 < baseStart_2027216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027228 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2027228 : Nat := 118140960795 + 2027228 * 2 ^ 59
def prefixEnd_2027228 : Nat := 4983230072969 + 3 ^ 40 * 2027228 * 2
def baseEnd_2027228 : Nat := 1040942360252899694826955

theorem tailTrace_2027228 : CollatzResearch.WordTrace tailWord_2027228 prefixEnd_2027228 1040942360252899694826955 := by
  unfold tailWord_2027228
  simp only [CollatzResearch.WordTrace]
  refine ⟨36969539749853326911645169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49292719666471102548860225 36969539749853326911645169)
  ·
    refine ⟨27727154812389995183733877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36969539749853326911645169 27727154812389995183733877)
    ·
      refine ⟨2599420763661562048475051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27727154812389995183733877 2599420763661562048475051)
      ·
        refine ⟨3899131145492343072712577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2599420763661562048475051 3899131145492343072712577)
        ·
          refine ⟨2924348359119257304534433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899131145492343072712577 2924348359119257304534433)
          ·
            refine ⟨2193261269339442978400825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2924348359119257304534433 2193261269339442978400825)
            ·
              refine ⟨1644945952004582233800619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193261269339442978400825 1644945952004582233800619)
              ·
                refine ⟨2467418928006873350700929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644945952004582233800619 2467418928006873350700929)
                ·
                  refine ⟨1850564196005155013025697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2467418928006873350700929 1850564196005155013025697)
                  ·
                    refine ⟨1387923147003866259769273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1850564196005155013025697 1387923147003866259769273)
                    ·
                      refine ⟨1040942360252899694826955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1387923147003866259769273 1040942360252899694826955)
                      ·
                        rfl

theorem cell23_2027228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2027228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027228 prefixEnd_2027228 := by exact prefixLift 2027228
  have htrace : WordTrace (prefixWord ++ tailWord_2027228) baseStart_2027228 baseEnd_2027228 := by
    simpa [prefixWord, tailWord_2027228, baseEnd_2027228] using wordTrace_append hprefix tailTrace_2027228
  have hstable : (prefixWord ++ tailWord_2027228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027228).length < 2 ^ (prefixWord ++ tailWord_2027228).sum := by decide
  have hdescent : baseEnd_2027228 < baseStart_2027228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027243 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 3, 4]
def baseStart_2027243 : Nat := 118140960795 + 2027243 * 2 ^ 59
def prefixEnd_2027243 : Nat := 4983230072969 + 3 ^ 40 * 2027243 * 2
def baseEnd_2027243 : Nat := 346983354154239045379795

theorem tailTrace_2027243 : CollatzResearch.WordTrace tailWord_2027243 prefixEnd_2027243 346983354154239045379795 := by
  unfold tailWord_2027243
  simp only [CollatzResearch.WordTrace]
  refine ⟨73939626594652311385086383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49293084396434874256724255 73939626594652311385086383)
  ·
    refine ⟨110909439891978467077629575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73939626594652311385086383 110909439891978467077629575)
    ·
      refine ⟨166364159837967700616444363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110909439891978467077629575 166364159837967700616444363)
      ·
        refine ⟨249546239756951550924666545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166364159837967700616444363 249546239756951550924666545)
        ·
          refine ⟨187159679817713663193499909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249546239756951550924666545 187159679817713663193499909)
          ·
            refine ⟨35092439965821311848781233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187159679817713663193499909 35092439965821311848781233)
            ·
              refine ⟨26319329974365983886585925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35092439965821311848781233 26319329974365983886585925)
              ·
                refine ⟨4934874370193621978734861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26319329974365983886585925 4934874370193621978734861)
                ·
                  refine ⟨1850577888822608242025573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4934874370193621978734861 1850577888822608242025573)
                  ·
                    refine ⟨346983354154239045379795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1850577888822608242025573 346983354154239045379795)
                    ·
                      rfl

theorem cell23_2027243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 4].length) (baseStart_2027243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027243 prefixEnd_2027243 := by exact prefixLift 2027243
  have htrace : WordTrace (prefixWord ++ tailWord_2027243) baseStart_2027243 baseEnd_2027243 := by
    simpa [prefixWord, tailWord_2027243, baseEnd_2027243] using wordTrace_append hprefix tailTrace_2027243
  have hstable : (prefixWord ++ tailWord_2027243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027243).length < 2 ^ (prefixWord ++ tailWord_2027243).sum := by decide
  have hdescent : baseEnd_2027243 < baseStart_2027243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027250 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2027250 : Nat := 118140960795 + 2027250 * 2 ^ 59
def prefixEnd_2027250 : Nat := 4983230072969 + 3 ^ 40 * 2027250 * 2
def baseEnd_2027250 : Nat := 1040953656827298608751853

theorem tailTrace_2027250 : CollatzResearch.WordTrace tailWord_2027250 prefixEnd_2027250 1040953656827298608751853 := by
  unfold tailWord_2027250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484970476406737895147801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49293254603751301053727469 18484970476406737895147801)
  ·
    refine ⟨13863727857305053421360851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18484970476406737895147801 13863727857305053421360851)
    ·
      refine ⟨20795591785957580132041277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13863727857305053421360851 20795591785957580132041277)
      ·
        refine ⟨7798346919734092549515479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20795591785957580132041277 7798346919734092549515479)
        ·
          refine ⟨11697520379601138824273219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7798346919734092549515479 11697520379601138824273219)
          ·
            refine ⟨17546280569401708236409829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11697520379601138824273219 17546280569401708236409829)
            ·
              refine ⟨3289927606762820294326843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17546280569401708236409829 3289927606762820294326843)
              ·
                refine ⟨4934891410144230441490265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3289927606762820294326843 4934891410144230441490265)
                ·
                  refine ⟨3701168557608172831117699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4934891410144230441490265 3701168557608172831117699)
                  ·
                    refine ⟨5551752836412259246676549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3701168557608172831117699 5551752836412259246676549)
                    ·
                      refine ⟨1040953656827298608751853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5551752836412259246676549 1040953656827298608751853)
                      ·
                        rfl

theorem cell23_2027250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2027250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027250 prefixEnd_2027250 := by exact prefixLift 2027250
  have htrace : WordTrace (prefixWord ++ tailWord_2027250) baseStart_2027250 baseEnd_2027250 := by
    simpa [prefixWord, tailWord_2027250, baseEnd_2027250] using wordTrace_append hprefix tailTrace_2027250
  have hstable : (prefixWord ++ tailWord_2027250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027250).length < 2 ^ (prefixWord ++ tailWord_2027250).sum := by decide
  have hdescent : baseEnd_2027250 < baseStart_2027250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027256 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 8]
def baseStart_2027256 : Nat := 118140960795 + 2027256 * 2 ^ 59
def prefixEnd_2027256 : Nat := 4983230072969 + 3 ^ 40 * 2027256 * 2
def baseEnd_2027256 : Nat := 115661859745691731697425

theorem tailTrace_2027256 : CollatzResearch.WordTrace tailWord_2027256 prefixEnd_2027256 115661859745691731697425 := by
  unfold tailWord_2027256
  simp only [CollatzResearch.WordTrace]
  refine ⟨36970050371802607302654811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49293400495736809736873081 36970050371802607302654811)
  ·
    refine ⟨55455075557703910953982217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36970050371802607302654811 55455075557703910953982217)
    ·
      refine ⟨41591306668277933215486663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55455075557703910953982217 41591306668277933215486663)
      ·
        refine ⟨62386960002416899823229995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41591306668277933215486663 62386960002416899823229995)
        ·
          refine ⟨93580440003625349734844993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62386960002416899823229995 93580440003625349734844993)
          ·
            refine ⟨70185330002719012301133745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93580440003625349734844993 70185330002719012301133745)
            ·
              refine ⟨52638997502039259225850309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70185330002719012301133745 52638997502039259225850309)
              ·
                refine ⟨9869812031632361104846933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52638997502039259225850309 9869812031632361104846933)
                ·
                  refine ⟨115661859745691731697425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9869812031632361104846933 115661859745691731697425)
                  ·
                    rfl

theorem cell23_2027256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 8].length) (baseStart_2027256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027256 prefixEnd_2027256 := by exact prefixLift 2027256
  have htrace : WordTrace (prefixWord ++ tailWord_2027256) baseStart_2027256 baseEnd_2027256 := by
    simpa [prefixWord, tailWord_2027256, baseEnd_2027256] using wordTrace_append hprefix tailTrace_2027256
  have hstable : (prefixWord ++ tailWord_2027256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027256).length < 2 ^ (prefixWord ++ tailWord_2027256).sum := by decide
  have hdescent : baseEnd_2027256 < baseStart_2027256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027320 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 1, 5]
def baseStart_2027320 : Nat := 118140960795 + 2027320 * 2 ^ 59
def prefixEnd_2027320 : Nat := 4983230072969 + 3 ^ 40 * 2027320 * 2
def baseEnd_2027320 : Nat := 346996533491037778292177

theorem tailTrace_2027320 : CollatzResearch.WordTrace tailWord_2027320 prefixEnd_2027320 346996533491037778292177 := by
  unfold tailWord_2027320
  simp only [CollatzResearch.WordTrace]
  refine ⟨36971217507686676767819707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49294956676915569023759609 36971217507686676767819707)
  ·
    refine ⟨55456826261530015151729561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36971217507686676767819707 55456826261530015151729561)
    ·
      refine ⟨41592619696147511363797171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55456826261530015151729561 41592619696147511363797171)
      ·
        refine ⟨62388929544221267045695757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41592619696147511363797171 62388929544221267045695757)
        ·
          refine ⟨23395848579082975142135909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62388929544221267045695757 23395848579082975142135909)
          ·
            refine ⟨4386721608578057839150483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23395848579082975142135909 4386721608578057839150483)
            ·
              refine ⟨6580082412867086758725725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4386721608578057839150483 6580082412867086758725725)
              ·
                refine ⟨2467530904825157534522147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6580082412867086758725725 2467530904825157534522147)
                ·
                  refine ⟨3701296357237736301783221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467530904825157534522147 3701296357237736301783221)
                  ·
                    refine ⟨346996533491037778292177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3701296357237736301783221 346996533491037778292177)
                    ·
                      rfl

theorem cell23_2027320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_2027320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027320 prefixEnd_2027320 := by exact prefixLift 2027320
  have htrace : WordTrace (prefixWord ++ tailWord_2027320) baseStart_2027320 baseEnd_2027320 := by
    simpa [prefixWord, tailWord_2027320, baseEnd_2027320] using wordTrace_append hprefix tailTrace_2027320
  have hstable : (prefixWord ++ tailWord_2027320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027320).length < 2 ^ (prefixWord ++ tailWord_2027320).sum := by decide
  have hdescent : baseEnd_2027320 < baseStart_2027320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027353 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_2027353 : Nat := 118140960795 + 2027353 * 2 ^ 59
def prefixEnd_2027353 : Nat := 4983230072969 + 3 ^ 40 * 2027353 * 2
def baseEnd_2027353 : Nat := 1041006545334711705763879

theorem tailTrace_2027353 : CollatzResearch.WordTrace tailWord_2027353 prefixEnd_2027353 1041006545334711705763879 := by
  unfold tailWord_2027353
  simp only [CollatzResearch.WordTrace]
  refine ⟨73943638624253800171590713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49295759082835866781060475 73943638624253800171590713)
  ·
    refine ⟨55457728968190350128693035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73943638624253800171590713 55457728968190350128693035)
    ·
      refine ⟨83186593452285525193039553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55457728968190350128693035 83186593452285525193039553)
      ·
        refine ⟨62389945089214143894779665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83186593452285525193039553 62389945089214143894779665)
        ·
          refine ⟨46792458816910607921084749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62389945089214143894779665 46792458816910607921084749)
          ·
            refine ⟨17547172056341477970406781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46792458816910607921084749 17547172056341477970406781)
            ·
              refine ⟨6580189521128054238902543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17547172056341477970406781 6580189521128054238902543)
              ·
                refine ⟨9870284281692081358353815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6580189521128054238902543 9870284281692081358353815)
                ·
                  refine ⟨14805426422538122037530723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9870284281692081358353815 14805426422538122037530723)
                  ·
                    refine ⟨22208139633807183056296085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14805426422538122037530723 22208139633807183056296085)
                    ·
                      refine ⟨1041006545334711705763879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22208139633807183056296085 1041006545334711705763879)
                      ·
                        rfl

theorem cell23_2027353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_2027353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027353 prefixEnd_2027353 := by exact prefixLift 2027353
  have htrace : WordTrace (prefixWord ++ tailWord_2027353) baseStart_2027353 baseEnd_2027353 := by
    simpa [prefixWord, tailWord_2027353, baseEnd_2027353] using wordTrace_append hprefix tailTrace_2027353
  have hstable : (prefixWord ++ tailWord_2027353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027353).length < 2 ^ (prefixWord ++ tailWord_2027353).sum := by decide
  have hdescent : baseEnd_2027353 < baseStart_2027353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027433 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_2027433 : Nat := 118140960795 + 2027433 * 2 ^ 59
def prefixEnd_2027433 : Nat := 4983230072969 + 3 ^ 40 * 2027433 * 2
def baseEnd_2027433 : Nat := 1041047623787071392763511

theorem tailTrace_2027433 : CollatzResearch.WordTrace tailWord_2027433 prefixEnd_2027433 1041047623787071392763511 := by
  unfold tailWord_2027433
  simp only [CollatzResearch.WordTrace]
  refine ⟨73946556463963973834502953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49297704309309315889668635 73946556463963973834502953)
  ·
    refine ⟨55459917347972980375877215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73946556463963973834502953 55459917347972980375877215)
    ·
      refine ⟨83189876021959470563815823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55459917347972980375877215 83189876021959470563815823)
      ·
        refine ⟨124784814032939205845723735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83189876021959470563815823 124784814032939205845723735)
        ·
          refine ⟨187177221049408808768585603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124784814032939205845723735 187177221049408808768585603)
          ·
            refine ⟨280765831574113213152878405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187177221049408808768585603 280765831574113213152878405)
            ·
              refine ⟨52643593420146227466164701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280765831574113213152878405 52643593420146227466164701)
              ·
                refine ⟨19741347532554835299811763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52643593420146227466164701 19741347532554835299811763)
                ·
                  refine ⟨29612021298832252949717645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741347532554835299811763 29612021298832252949717645)
                  ·
                    refine ⟨11104507987062094856144117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29612021298832252949717645 11104507987062094856144117)
                    ·
                      refine ⟨1041047623787071392763511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11104507987062094856144117 1041047623787071392763511)
                      ·
                        rfl

theorem cell23_2027433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_2027433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027433 prefixEnd_2027433 := by exact prefixLift 2027433
  have htrace : WordTrace (prefixWord ++ tailWord_2027433) baseStart_2027433 baseEnd_2027433 := by
    simpa [prefixWord, tailWord_2027433, baseEnd_2027433] using wordTrace_append hprefix tailTrace_2027433
  have hstable : (prefixWord ++ tailWord_2027433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027433).length < 2 ^ (prefixWord ++ tailWord_2027433).sum := by decide
  have hdescent : baseEnd_2027433 < baseStart_2027433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027464 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_2027464 : Nat := 118140960795 + 2027464 * 2 ^ 59
def prefixEnd_2027464 : Nat := 4983230072969 + 3 ^ 40 * 2027464 * 2
def baseEnd_2027464 : Nat := 1041063541687360771475869

theorem tailTrace_2027464 : CollatzResearch.WordTrace tailWord_2027464 prefixEnd_2027464 1041063541687360771475869 := by
  unfold tailWord_2027464
  simp only [CollatzResearch.WordTrace]
  refine ⟨36973843563425833064440723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49298458084567777419254297 36973843563425833064440723)
  ·
    refine ⟨55460765345138749596661085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36973843563425833064440723 55460765345138749596661085)
    ·
      refine ⟨20797787004427031098747907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55460765345138749596661085 20797787004427031098747907)
      ·
        refine ⟨31196680506640546648121861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20797787004427031098747907 31196680506640546648121861)
        ·
          refine ⟨5849377594995102496522849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31196680506640546648121861 5849377594995102496522849)
          ·
            refine ⟨4387033196246326872392137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5849377594995102496522849 4387033196246326872392137)
            ·
              refine ⟨3290274897184745154294103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4387033196246326872392137 3290274897184745154294103)
              ·
                refine ⟨4935412345777117731441155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3290274897184745154294103 4935412345777117731441155)
                ·
                  refine ⟨7403118518665676597161733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935412345777117731441155 7403118518665676597161733)
                  ·
                    refine ⟨1388084722249814361967825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7403118518665676597161733 1388084722249814361967825)
                    ·
                      refine ⟨1041063541687360771475869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1388084722249814361967825 1041063541687360771475869)
                      ·
                        rfl

theorem cell23_2027464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_2027464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027464 prefixEnd_2027464 := by exact prefixLift 2027464
  have htrace : WordTrace (prefixWord ++ tailWord_2027464) baseStart_2027464 baseEnd_2027464 := by
    simpa [prefixWord, tailWord_2027464, baseEnd_2027464] using wordTrace_append hprefix tailTrace_2027464
  have hstable : (prefixWord ++ tailWord_2027464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027464).length < 2 ^ (prefixWord ++ tailWord_2027464).sum := by decide
  have hdescent : baseEnd_2027464 < baseStart_2027464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027470 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_2027470 : Nat := 118140960795 + 2027470 * 2 ^ 59
def prefixEnd_2027470 : Nat := 4983230072969 + 3 ^ 40 * 2027470 * 2
def baseEnd_2027470 : Nat := 115674069174587527555649

theorem tailTrace_2027470 : CollatzResearch.WordTrace tailWord_2027470 prefixEnd_2027470 115674069174587527555649 := by
  unfold tailWord_2027470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243488245603741144199983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49298603976553286102399909 9243488245603741144199983)
  ·
    refine ⟨13865232368405611716299975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9243488245603741144199983 13865232368405611716299975)
    ·
      refine ⟨20797848552608417574449963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13865232368405611716299975 20797848552608417574449963)
      ·
        refine ⟨31196772828912626361674945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20797848552608417574449963 31196772828912626361674945)
        ·
          refine ⟨23397579621684469771256209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31196772828912626361674945 23397579621684469771256209)
          ·
            refine ⟨17548184716263352328442157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23397579621684469771256209 17548184716263352328442157)
            ·
              refine ⟨6580569268598757123165809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17548184716263352328442157 6580569268598757123165809)
              ·
                refine ⟨4935426951449067842374357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6580569268598757123165809 4935426951449067842374357)
                ·
                  refine ⟨115674069174587527555649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4935426951449067842374357 115674069174587527555649)
                  ·
                    rfl

theorem cell23_2027470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_2027470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027470 prefixEnd_2027470 := by exact prefixLift 2027470
  have htrace : WordTrace (prefixWord ++ tailWord_2027470) baseStart_2027470 baseEnd_2027470 := by
    simpa [prefixWord, tailWord_2027470, baseEnd_2027470] using wordTrace_append hprefix tailTrace_2027470
  have hstable : (prefixWord ++ tailWord_2027470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027470).length < 2 ^ (prefixWord ++ tailWord_2027470).sum := by decide
  have hdescent : baseEnd_2027470 < baseStart_2027470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027480 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_2027480 : Nat := 118140960795 + 2027480 * 2 ^ 59
def prefixEnd_2027480 : Nat := 4983230072969 + 3 ^ 40 * 2027480 * 2
def baseEnd_2027480 : Nat := 1041071757377832708875795

theorem tailTrace_2027480 : CollatzResearch.WordTrace tailWord_2027480 prefixEnd_2027480 1041071757377832708875795 := by
  unfold tailWord_2027480
  simp only [CollatzResearch.WordTrace]
  refine ⟨36974135347396850430731947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49298847129862467240975929 36974135347396850430731947)
  ·
    refine ⟨55461203021095275646097921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36974135347396850430731947 55461203021095275646097921)
    ·
      refine ⟨41595902265821456734573441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55461203021095275646097921 41595902265821456734573441)
      ·
        refine ⟨31196926699366092550930081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41595902265821456734573441 31196926699366092550930081)
        ·
          refine ⟨23397695024524569413197561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31196926699366092550930081 23397695024524569413197561)
          ·
            refine ⟨17548271268393427059898171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23397695024524569413197561 17548271268393427059898171)
            ·
              refine ⟨26322406902590140589847257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17548271268393427059898171 26322406902590140589847257)
              ·
                refine ⟨19741805176942605442385443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26322406902590140589847257 19741805176942605442385443)
                ·
                  refine ⟨29612707765413908163578165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19741805176942605442385443 29612707765413908163578165)
                  ·
                    refine ⟨2776191353007553890335453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29612707765413908163578165 2776191353007553890335453)
                    ·
                      refine ⟨1041071757377832708875795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2776191353007553890335453 1041071757377832708875795)
                      ·
                        rfl

theorem cell23_2027480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_2027480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027480 prefixEnd_2027480 := by exact prefixLift 2027480
  have htrace : WordTrace (prefixWord ++ tailWord_2027480) baseStart_2027480 baseEnd_2027480 := by
    simpa [prefixWord, tailWord_2027480, baseEnd_2027480] using wordTrace_append hprefix tailTrace_2027480
  have hstable : (prefixWord ++ tailWord_2027480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027480).length < 2 ^ (prefixWord ++ tailWord_2027480).sum := by decide
  have hdescent : baseEnd_2027480 < baseStart_2027480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027485 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_2027485 : Nat := 118140960795 + 2027485 * 2 ^ 59
def prefixEnd_2027485 : Nat := 4983230072969 + 3 ^ 40 * 2027485 * 2
def baseEnd_2027485 : Nat := 1041074324781105189313273

theorem tailTrace_2027485 : CollatzResearch.WordTrace tailWord_2027485 prefixEnd_2027485 1041074324781105189313273 := by
  unfold tailWord_2027485
  simp only [CollatzResearch.WordTrace]
  refine ⟨73948453059775586715395909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49298968706517057810263939 73948453059775586715395909)
  ·
    refine ⟨13865334948707922509136733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73948453059775586715395909 13865334948707922509136733)
    ·
      refine ⟨5199500605765470940926275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13865334948707922509136733 5199500605765470940926275)
      ·
        refine ⟨7799250908648206411389413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5199500605765470940926275 7799250908648206411389413)
        ·
          refine ⟨1462359545371538702135515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7799250908648206411389413 1462359545371538702135515)
          ·
            refine ⟨2193539318057308053203273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1462359545371538702135515 2193539318057308053203273)
            ·
              refine ⟨1645154488542981039902455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193539318057308053203273 1645154488542981039902455)
              ·
                refine ⟨2467731732814471559853683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645154488542981039902455 2467731732814471559853683)
                ·
                  refine ⟨3701597599221707339780525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467731732814471559853683 3701597599221707339780525)
                  ·
                    refine ⟨1388099099708140252417697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3701597599221707339780525 1388099099708140252417697)
                    ·
                      refine ⟨1041074324781105189313273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1388099099708140252417697 1041074324781105189313273)
                      ·
                        rfl

theorem cell23_2027485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_2027485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027485 prefixEnd_2027485 := by exact prefixLift 2027485
  have htrace : WordTrace (prefixWord ++ tailWord_2027485) baseStart_2027485 baseEnd_2027485 := by
    simpa [prefixWord, tailWord_2027485, baseEnd_2027485] using wordTrace_append hprefix tailTrace_2027485
  have hstable : (prefixWord ++ tailWord_2027485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027485).length < 2 ^ (prefixWord ++ tailWord_2027485).sum := by decide
  have hdescent : baseEnd_2027485 < baseStart_2027485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027487 : List Nat := [1, 1, 2, 3, 4, 1, 1, 5, 5]
def baseStart_2027487 : Nat := 118140960795 + 2027487 * 2 ^ 59
def prefixEnd_2027487 : Nat := 4983230072969 + 3 ^ 40 * 2027487 * 2
def baseEnd_2027487 : Nat := 115675039082490464609807

theorem tailTrace_2027487 : CollatzResearch.WordTrace tailWord_2027487 prefixEnd_2027487 115675039082490464609807 := by
  unfold tailWord_2027487
  simp only [CollatzResearch.WordTrace]
  refine ⟨73948526005768341056968715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49299017337178894037979143 73948526005768341056968715)
  ·
    refine ⟨110922789008652511585453073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73948526005768341056968715 110922789008652511585453073)
    ·
      refine ⟨83192091756489383689089805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110922789008652511585453073 83192091756489383689089805)
      ·
        refine ⟨31197034408683518883408677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83192091756489383689089805 31197034408683518883408677)
        ·
          refine ⟨5849443951628159790639127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31197034408683518883408677 5849443951628159790639127)
          ·
            refine ⟨8774165927442239685958691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5849443951628159790639127 8774165927442239685958691)
            ·
              refine ⟨13161248891163359528938037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774165927442239685958691 13161248891163359528938037)
              ·
                refine ⟨1233867083546564955837941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13161248891163359528938037 1233867083546564955837941)
                ·
                  refine ⟨115675039082490464609807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1233867083546564955837941 115675039082490464609807)
                  ·
                    rfl

theorem cell23_2027487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 5, 5].length) (baseStart_2027487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027487 prefixEnd_2027487 := by exact prefixLift 2027487
  have htrace : WordTrace (prefixWord ++ tailWord_2027487) baseStart_2027487 baseEnd_2027487 := by
    simpa [prefixWord, tailWord_2027487, baseEnd_2027487] using wordTrace_append hprefix tailTrace_2027487
  have hstable : (prefixWord ++ tailWord_2027487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027487).length < 2 ^ (prefixWord ++ tailWord_2027487).sum := by decide
  have hdescent : baseEnd_2027487 < baseStart_2027487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027500 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_2027500 : Nat := 118140960795 + 2027500 * 2 ^ 59
def prefixEnd_2027500 : Nat := 4983230072969 + 3 ^ 40 * 2027500 * 2
def baseEnd_2027500 : Nat := 347027342330307543541901

theorem tailTrace_2027500 : CollatzResearch.WordTrace tailWord_2027500 prefixEnd_2027500 347027342330307543541901 := by
  unfold tailWord_2027500
  simp only [CollatzResearch.WordTrace]
  refine ⟨36974500077360622138595977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49299333436480829518127969 36974500077360622138595977)
  ·
    refine ⟨27730875058020466603946983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36974500077360622138595977 27730875058020466603946983)
    ·
      refine ⟨41596312587030699905920475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27730875058020466603946983 41596312587030699905920475)
      ·
        refine ⟨62394468880546049858880713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41596312587030699905920475 62394468880546049858880713)
        ·
          refine ⟨46795851660409537394160535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62394468880546049858880713 46795851660409537394160535)
          ·
            refine ⟨70193777490614306091240803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46795851660409537394160535 70193777490614306091240803)
            ·
              refine ⟨105290666235921459136861205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70193777490614306091240803 105290666235921459136861205)
              ·
                refine ⟨4935499979808818397040369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105290666235921459136861205 4935499979808818397040369)
                ·
                  refine ⟨3701624984856613797780277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4935499979808818397040369 3701624984856613797780277)
                  ·
                    refine ⟨347027342330307543541901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3701624984856613797780277 347027342330307543541901)
                    ·
                      rfl

theorem cell23_2027500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_2027500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027500 prefixEnd_2027500 := by exact prefixLift 2027500
  have htrace : WordTrace (prefixWord ++ tailWord_2027500) baseStart_2027500 baseEnd_2027500 := by
    simpa [prefixWord, tailWord_2027500, baseEnd_2027500] using wordTrace_append hprefix tailTrace_2027500
  have hstable : (prefixWord ++ tailWord_2027500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027500).length < 2 ^ (prefixWord ++ tailWord_2027500).sum := by decide
  have hdescent : baseEnd_2027500 < baseStart_2027500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027520 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_2027520 : Nat := 118140960795 + 2027520 * 2 ^ 59
def prefixEnd_2027520 : Nat := 4983230072969 + 3 ^ 40 * 2027520 * 2
def baseEnd_2027520 : Nat := 1041092296604012552375611

theorem tailTrace_2027520 : CollatzResearch.WordTrace tailWord_2027520 prefixEnd_2027520 1041092296604012552375611 := by
  unfold tailWord_2027520
  simp only [CollatzResearch.WordTrace]
  refine ⟨36974864807324393846460007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49299819743099191795280009 36974864807324393846460007)
  ·
    refine ⟨55462297210986590769690011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36974864807324393846460007 55462297210986590769690011)
    ·
      refine ⟨83193445816479886154535017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55462297210986590769690011 83193445816479886154535017)
      ·
        refine ⟨62395084362359914615901263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83193445816479886154535017 62395084362359914615901263)
        ·
          refine ⟨93592626543539871923851895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62395084362359914615901263 93592626543539871923851895)
          ·
            refine ⟨140388939815309807885777843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93592626543539871923851895 140388939815309807885777843)
            ·
              refine ⟨210583409722964711828666765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140388939815309807885777843 210583409722964711828666765)
              ·
                refine ⟨78968778646111766935750037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210583409722964711828666765 78968778646111766935750037)
                ·
                  refine ⟨3701661499036489075113283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78968778646111766935750037 3701661499036489075113283)
                  ·
                    refine ⟨5552492248554733612669925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3701661499036489075113283 5552492248554733612669925)
                    ·
                      refine ⟨1041092296604012552375611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5552492248554733612669925 1041092296604012552375611)
                      ·
                        rfl

theorem cell23_2027520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_2027520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027520 prefixEnd_2027520 := by exact prefixLift 2027520
  have htrace : WordTrace (prefixWord ++ tailWord_2027520) baseStart_2027520 baseEnd_2027520 := by
    simpa [prefixWord, tailWord_2027520, baseEnd_2027520] using wordTrace_append hprefix tailTrace_2027520
  have hstable : (prefixWord ++ tailWord_2027520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027520).length < 2 ^ (prefixWord ++ tailWord_2027520).sum := by decide
  have hdescent : baseEnd_2027520 < baseStart_2027520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027557 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_2027557 : Nat := 118140960795 + 2027557 * 2 ^ 59
def prefixEnd_2027557 : Nat := 4983230072969 + 3 ^ 40 * 2027557 * 2
def baseEnd_2027557 : Nat := 1041111295388228907612941

theorem tailTrace_2027557 : CollatzResearch.WordTrace tailWord_2027557 prefixEnd_2027557 1041111295388228907612941 := by
  unfold tailWord_2027557
  simp only [CollatzResearch.WordTrace]
  refine ⟨73951079115514743012016925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49300719410343162008011283 73951079115514743012016925)
  ·
    refine ⟨27731654668318028629506347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73951079115514743012016925 27731654668318028629506347)
    ·
      refine ⟨41597482002477042944259521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27731654668318028629506347 41597482002477042944259521)
      ·
        refine ⟨31198111501857782208194641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41597482002477042944259521 31198111501857782208194641)
        ·
          refine ⟨23398583626393336656145981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31198111501857782208194641 23398583626393336656145981)
          ·
            refine ⟨8774468859897501246054743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23398583626393336656145981 8774468859897501246054743)
            ·
              refine ⟨13161703289846251869082115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8774468859897501246054743 13161703289846251869082115)
              ·
                refine ⟨19742554934769377803623173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13161703289846251869082115 19742554934769377803623173)
                ·
                  refine ⟨3701729050269258338179345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19742554934769377803623173 3701729050269258338179345)
                  ·
                    refine ⟨2776296787701943753634509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3701729050269258338179345 2776296787701943753634509)
                    ·
                      refine ⟨1041111295388228907612941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2776296787701943753634509 1041111295388228907612941)
                      ·
                        rfl

theorem cell23_2027557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_2027557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027557 prefixEnd_2027557 := by exact prefixLift 2027557
  have htrace : WordTrace (prefixWord ++ tailWord_2027557) baseStart_2027557 baseEnd_2027557 := by
    simpa [prefixWord, tailWord_2027557, baseEnd_2027557] using wordTrace_append hprefix tailTrace_2027557
  have hstable : (prefixWord ++ tailWord_2027557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027557).length < 2 ^ (prefixWord ++ tailWord_2027557).sum := by decide
  have hdescent : baseEnd_2027557 < baseStart_2027557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027574 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2027574 : Nat := 118140960795 + 2027574 * 2 ^ 59
def prefixEnd_2027574 : Nat := 4983230072969 + 3 ^ 40 * 2027574 * 2
def baseEnd_2027574 : Nat := 1041120024559355341100363

theorem tailTrace_2027574 : CollatzResearch.WordTrace tailWord_2027574 prefixEnd_2027574 1041120024559355341100363 := by
  unfold tailWord_2027574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4621981197278322182211611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49301132770968769943590517 4621981197278322182211611)
  ·
    refine ⟨6932971795917483273317417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4621981197278322182211611 6932971795917483273317417)
    ·
      refine ⟨5199728846938112454988063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6932971795917483273317417 5199728846938112454988063)
      ·
        refine ⟨7799593270407168682482095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5199728846938112454988063 7799593270407168682482095)
        ·
          refine ⟨11699389905610753023723143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7799593270407168682482095 11699389905610753023723143)
          ·
            refine ⟨17549084858416129535584715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11699389905610753023723143 17549084858416129535584715)
            ·
              refine ⟨26323627287624194303377073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17549084858416129535584715 26323627287624194303377073)
              ·
                refine ⟨19742720465718145727532805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26323627287624194303377073 19742720465718145727532805)
                ·
                  refine ⟨3701760087322152323912401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19742720465718145727532805 3701760087322152323912401)
                  ·
                    refine ⟨2776320065491614242934301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3701760087322152323912401 2776320065491614242934301)
                    ·
                      refine ⟨1041120024559355341100363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2776320065491614242934301 1041120024559355341100363)
                      ·
                        rfl

theorem cell23_2027574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2027574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027574 prefixEnd_2027574 := by exact prefixLift 2027574
  have htrace : WordTrace (prefixWord ++ tailWord_2027574) baseStart_2027574 baseEnd_2027574 := by
    simpa [prefixWord, tailWord_2027574, baseEnd_2027574] using wordTrace_append hprefix tailTrace_2027574
  have hstable : (prefixWord ++ tailWord_2027574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027574).length < 2 ^ (prefixWord ++ tailWord_2027574).sum := by decide
  have hdescent : baseEnd_2027574 < baseStart_2027574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027607 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 1, 5]
def baseStart_2027607 : Nat := 118140960795 + 2027607 * 2 ^ 59
def prefixEnd_2027607 : Nat := 4983230072969 + 3 ^ 40 * 2027607 * 2
def baseEnd_2027607 : Nat := 347045656473651237329237

theorem tailTrace_2027607 : CollatzResearch.WordTrace tailWord_2027607 prefixEnd_2027607 347045656473651237329237 := by
  unfold tailWord_2027607
  simp only [CollatzResearch.WordTrace]
  refine ⟨73952902765333601551337075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49301935176889067700891383 73952902765333601551337075)
  ·
    refine ⟨110929354148000402327005613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73952902765333601551337075 110929354148000402327005613)
    ·
      refine ⟨41598507805500150872627105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110929354148000402327005613 41598507805500150872627105)
      ·
        refine ⟨31198880854125113154470329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41598507805500150872627105 31198880854125113154470329)
        ·
          refine ⟨23399160640593834865852747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31198880854125113154470329 23399160640593834865852747)
          ·
            refine ⟨35098740960890752298779121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23399160640593834865852747 35098740960890752298779121)
            ·
              refine ⟨26324055720668064224084341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35098740960890752298779121 26324055720668064224084341)
              ·
                refine ⟨2467880223812631021007907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26324055720668064224084341 2467880223812631021007907)
                ·
                  refine ⟨3701820335718946531511861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467880223812631021007907 3701820335718946531511861)
                  ·
                    refine ⟨347045656473651237329237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3701820335718946531511861 347045656473651237329237)
                    ·
                      rfl

theorem cell23_2027607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_2027607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027607 prefixEnd_2027607 := by exact prefixLift 2027607
  have htrace : WordTrace (prefixWord ++ tailWord_2027607) baseStart_2027607 baseEnd_2027607 := by
    simpa [prefixWord, tailWord_2027607, baseEnd_2027607] using wordTrace_append hprefix tailTrace_2027607
  have hstable : (prefixWord ++ tailWord_2027607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027607).length < 2 ^ (prefixWord ++ tailWord_2027607).sum := by decide
  have hdescent : baseEnd_2027607 < baseStart_2027607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027657 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_2027657 : Nat := 118140960795 + 2027657 * 2 ^ 59
def prefixEnd_2027657 : Nat := 4983230072969 + 3 ^ 40 * 2027657 * 2
def baseEnd_2027657 : Nat := 1041162643453678516362481

theorem tailTrace_2027657 : CollatzResearch.WordTrace tailWord_2027657 prefixEnd_2027657 1041162643453678516362481 := by
  unfold tailWord_2027657
  simp only [CollatzResearch.WordTrace]
  refine ⟨73954726415152460090657225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49303150943434973393771483 73954726415152460090657225)
  ·
    refine ⟨55466044811364345067992919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73954726415152460090657225 55466044811364345067992919)
    ·
      refine ⟨83199067217046517601989379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55466044811364345067992919 83199067217046517601989379)
      ·
        refine ⟨124798600825569776402984069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83199067217046517601989379 124798600825569776402984069)
        ·
          refine ⟨23399737654794333075559513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124798600825569776402984069 23399737654794333075559513)
          ·
            refine ⟨17549803241095749806669635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23399737654794333075559513 17549803241095749806669635)
            ·
              refine ⟨26324704861643624710004453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17549803241095749806669635 26324704861643624710004453)
              ·
                refine ⟨4935882161558179633125835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26324704861643624710004453 4935882161558179633125835)
                ·
                  refine ⟨7403823242337269449688753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4935882161558179633125835 7403823242337269449688753)
                  ·
                    refine ⟨5552867431752952087266565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7403823242337269449688753 5552867431752952087266565)
                    ·
                      refine ⟨1041162643453678516362481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5552867431752952087266565 1041162643453678516362481)
                      ·
                        rfl

theorem cell23_2027657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_2027657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027657 prefixEnd_2027657 := by exact prefixLift 2027657
  have htrace : WordTrace (prefixWord ++ tailWord_2027657) baseStart_2027657 baseEnd_2027657 := by
    simpa [prefixWord, tailWord_2027657, baseEnd_2027657] using wordTrace_append hprefix tailTrace_2027657
  have hstable : (prefixWord ++ tailWord_2027657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027657).length < 2 ^ (prefixWord ++ tailWord_2027657).sum := by decide
  have hdescent : baseEnd_2027657 < baseStart_2027657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027664 : List Nat := [2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3]
def baseStart_2027664 : Nat := 118140960795 + 2027664 * 2 ^ 59
def prefixEnd_2027664 : Nat := 4983230072969 + 3 ^ 40 * 2027664 * 2
def baseEnd_2027664 : Nat := 1041166237818259988974949

theorem tailTrace_2027664 : CollatzResearch.WordTrace tailWord_2027664 prefixEnd_2027664 1041166237818259988974949 := by
  unfold tailWord_2027664
  simp only [CollatzResearch.WordTrace]
  refine ⟨36977490863063550143081023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49303321150751400190774697 36977490863063550143081023)
  ·
    refine ⟨55466236294595325214621535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36977490863063550143081023 55466236294595325214621535)
    ·
      refine ⟨83199354441892987821932303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55466236294595325214621535 83199354441892987821932303)
      ·
        refine ⟨124799031662839481732898455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83199354441892987821932303 124799031662839481732898455)
        ·
          refine ⟨187198547494259222599347683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124799031662839481732898455 187198547494259222599347683)
          ·
            refine ⟨280797821241388833899021525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187198547494259222599347683 280797821241388833899021525)
            ·
              refine ⟨6581198935345050794508317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 280797821241388833899021525 6581198935345050794508317)
              ·
                refine ⟨2467949600754394047940619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6581198935345050794508317 2467949600754394047940619)
                ·
                  refine ⟨3701924401131591071910929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2467949600754394047940619 3701924401131591071910929)
                  ·
                    refine ⟨2776443300848693303933197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3701924401131591071910929 2776443300848693303933197)
                    ·
                      refine ⟨1041166237818259988974949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2776443300848693303933197 1041166237818259988974949)
                      ·
                        rfl

theorem cell23_2027664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 3].length) (baseStart_2027664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027664 prefixEnd_2027664 := by exact prefixLift 2027664
  have htrace : WordTrace (prefixWord ++ tailWord_2027664) baseStart_2027664 baseEnd_2027664 := by
    simpa [prefixWord, tailWord_2027664, baseEnd_2027664] using wordTrace_append hprefix tailTrace_2027664
  have hstable : (prefixWord ++ tailWord_2027664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027664).length < 2 ^ (prefixWord ++ tailWord_2027664).sum := by decide
  have hdescent : baseEnd_2027664 < baseStart_2027664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027824 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_2027824 : Nat := 118140960795 + 2027824 * 2 ^ 59
def prefixEnd_2027824 : Nat := 4983230072969 + 3 ^ 40 * 2027824 * 2
def baseEnd_2027824 : Nat := 1041248394722979362974213

theorem tailTrace_2027824 : CollatzResearch.WordTrace tailWord_2027824 prefixEnd_2027824 1041248394722979362974213 := by
  unfold tailWord_2027824
  simp only [CollatzResearch.WordTrace]
  refine ⟨36980408702773723805993263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49307211603698298407991017 36980408702773723805993263)
  ·
    refine ⟨55470613054160585708989895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36980408702773723805993263 55470613054160585708989895)
    ·
      refine ⟨83205919581240878563484843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55470613054160585708989895 83205919581240878563484843)
      ·
        refine ⟨124808879371861317845227265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83205919581240878563484843 124808879371861317845227265)
        ·
          refine ⟨93606659528895988383920449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124808879371861317845227265 93606659528895988383920449)
          ·
            refine ⟨70204994646671991287940337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93606659528895988383920449 70204994646671991287940337)
            ·
              refine ⟨52653745985003993465955253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70204994646671991287940337 52653745985003993465955253)
              ·
                refine ⟨4936288686094124387433305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52653745985003993465955253 4936288686094124387433305)
                ·
                  refine ⟨3702216514570593290574979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936288686094124387433305 3702216514570593290574979)
                  ·
                    refine ⟨5553324771855889935862469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3702216514570593290574979 5553324771855889935862469)
                    ·
                      refine ⟨1041248394722979362974213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5553324771855889935862469 1041248394722979362974213)
                      ·
                        rfl

theorem cell23_2027824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_2027824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027824 prefixEnd_2027824 := by exact prefixLift 2027824
  have htrace : WordTrace (prefixWord ++ tailWord_2027824) baseStart_2027824 baseEnd_2027824 := by
    simpa [prefixWord, tailWord_2027824, baseEnd_2027824] using wordTrace_append hprefix tailTrace_2027824
  have hstable : (prefixWord ++ tailWord_2027824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027824).length < 2 ^ (prefixWord ++ tailWord_2027824).sum := by decide
  have hdescent : baseEnd_2027824 < baseStart_2027824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027867 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8]
def baseStart_2027867 : Nat := 118140960795 + 2027867 * 2 ^ 59
def prefixEnd_2027867 : Nat := 4983230072969 + 3 ^ 40 * 2027867 * 2
def baseEnd_2027867 : Nat := 1041270474391122694736515

theorem tailTrace_2027867 : CollatzResearch.WordTrace tailWord_2027867 prefixEnd_2027867 1041270474391122694736515 := by
  unfold tailWord_2027867
  simp only [CollatzResearch.WordTrace]
  refine ⟨73962385744391665955801855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49308257162927777303867903 73962385744391665955801855)
  ·
    refine ⟨110943578616587498933702783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73962385744391665955801855 110943578616587498933702783)
    ·
      refine ⟨166415367924881248400554175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110943578616587498933702783 166415367924881248400554175)
      ·
        refine ⟨249623051887321872600831263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166415367924881248400554175 249623051887321872600831263)
        ·
          refine ⟨374434577830982808901246895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249623051887321872600831263 374434577830982808901246895)
          ·
            refine ⟨561651866746474213351870343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374434577830982808901246895 561651866746474213351870343)
            ·
              refine ⟨842477800119711320027805515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561651866746474213351870343 842477800119711320027805515)
              ·
                refine ⟨1263716700179566980041708273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842477800119711320027805515 1263716700179566980041708273)
                ·
                  refine ⟨947787525134675235031281205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1263716700179566980041708273 947787525134675235031281205)
                  ·
                    refine ⟨88855080481375803284182613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 947787525134675235031281205 88855080481375803284182613)
                    ·
                      refine ⟨1041270474391122694736515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 88855080481375803284182613 1041270474391122694736515)
                      ·
                        rfl

theorem cell23_2027867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_2027867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027867 prefixEnd_2027867 := by exact prefixLift 2027867
  have htrace : WordTrace (prefixWord ++ tailWord_2027867) baseStart_2027867 baseEnd_2027867 := by
    simpa [prefixWord, tailWord_2027867, baseEnd_2027867] using wordTrace_append hprefix tailTrace_2027867
  have hstable : (prefixWord ++ tailWord_2027867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027867).length < 2 ^ (prefixWord ++ tailWord_2027867).sum := by decide
  have hdescent : baseEnd_2027867 < baseStart_2027867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027928 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 1, 5]
def baseStart_2027928 : Nat := 118140960795 + 2027928 * 2 ^ 59
def prefixEnd_2027928 : Nat := 4983230072969 + 3 ^ 40 * 2027928 * 2
def baseEnd_2027928 : Nat := 347100598903682318691245

theorem tailTrace_2027928 : CollatzResearch.WordTrace tailWord_2027928 prefixEnd_2027928 347100598903682318691245 := by
  unfold tailWord_2027928
  simp only [CollatzResearch.WordTrace]
  refine ⟨36982305298585336686886219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49309740398113782249181625 36982305298585336686886219)
  ·
    refine ⟨55473457947878005030329329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36982305298585336686886219 55473457947878005030329329)
    ·
      refine ⟨41605093460908503772746997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55473457947878005030329329 41605093460908503772746997)
      ·
        refine ⟨3900477511960172228695031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41605093460908503772746997 3900477511960172228695031)
        ·
          refine ⟨5850716267940258343042547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900477511960172228695031 5850716267940258343042547)
          ·
            refine ⟨8776074401910387514563821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850716267940258343042547 8776074401910387514563821)
            ·
              refine ⟨3291027900716395317961433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8776074401910387514563821 3291027900716395317961433)
              ·
                refine ⟨2468270925537296488471075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3291027900716395317961433 2468270925537296488471075)
                ·
                  refine ⟨3702406388305944732706613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468270925537296488471075 3702406388305944732706613)
                  ·
                    refine ⟨347100598903682318691245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3702406388305944732706613 347100598903682318691245)
                    ·
                      rfl

theorem cell23_2027928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_2027928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027928 prefixEnd_2027928 := by exact prefixLift 2027928
  have htrace : WordTrace (prefixWord ++ tailWord_2027928) baseStart_2027928 baseEnd_2027928 := by
    simpa [prefixWord, tailWord_2027928, baseEnd_2027928] using wordTrace_append hprefix tailTrace_2027928
  have hstable : (prefixWord ++ tailWord_2027928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027928).length < 2 ^ (prefixWord ++ tailWord_2027928).sum := by decide
  have hdescent : baseEnd_2027928 < baseStart_2027928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2027988 : List Nat := [2, 4, 1, 2, 2, 2, 3, 7]
def baseStart_2027988 : Nat := 118140960795 + 2027988 * 2 ^ 59
def prefixEnd_2027988 : Nat := 4983230072969 + 3 ^ 40 * 2027988 * 2
def baseEnd_2027988 : Nat := 38567874279641360049017

theorem tailTrace_2027988 : CollatzResearch.WordTrace tailWord_2027988 prefixEnd_2027988 38567874279641360049017 := by
  unfold tailWord_2027988
  simp only [CollatzResearch.WordTrace]
  refine ⟨36983399488476651810478309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49311199317968869080637745 36983399488476651810478309)
  ·
    refine ⟨6934387404089372214464683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36983399488476651810478309 6934387404089372214464683)
    ·
      refine ⟨10401581106134058321697025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6934387404089372214464683 10401581106134058321697025)
      ·
        refine ⟨7801185829600543741272769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10401581106134058321697025 7801185829600543741272769)
        ·
          refine ⟨5850889372200407805954577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7801185829600543741272769 5850889372200407805954577)
          ·
            refine ⟨4388167029150305854465933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5850889372200407805954577 4388167029150305854465933)
            ·
              refine ⟨1645562635931364695424725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4388167029150305854465933 1645562635931364695424725)
              ·
                refine ⟨38567874279641360049017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1645562635931364695424725 38567874279641360049017)
                ·
                  rfl

theorem cell23_2027988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 7].length) (baseStart_2027988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2027988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2027988 prefixEnd_2027988 := by exact prefixLift 2027988
  have htrace : WordTrace (prefixWord ++ tailWord_2027988) baseStart_2027988 baseEnd_2027988 := by
    simpa [prefixWord, tailWord_2027988, baseEnd_2027988] using wordTrace_append hprefix tailTrace_2027988
  have hstable : (prefixWord ++ tailWord_2027988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2027988).length < 2 ^ (prefixWord ++ tailWord_2027988).sum := by decide
  have hdescent : baseEnd_2027988 < baseStart_2027988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2027988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028045 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2028045 : Nat := 118140960795 + 2028045 * 2 ^ 59
def prefixEnd_2028045 : Nat := 4983230072969 + 3 ^ 40 * 2028045 * 2
def baseEnd_2028045 : Nat := 1041361873947622998310697

theorem tailTrace_2028045 : CollatzResearch.WordTrace tailWord_2028045 prefixEnd_2028045 1041361873947622998310697 := by
  unfold tailWord_2028045
  simp only [CollatzResearch.WordTrace]
  refine ⟨73968877937746802355781589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49312585291831201570521059 73968877937746802355781589)
  ·
    refine ⟨1733645576665940680213631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 73968877937746802355781589 1733645576665940680213631)
    ·
      refine ⟨2600468364998911020320447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733645576665940680213631 2600468364998911020320447)
      ·
        refine ⟨3900702547498366530480671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2600468364998911020320447 3900702547498366530480671)
        ·
          refine ⟨5851053821247549795721007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900702547498366530480671 5851053821247549795721007)
          ·
            refine ⟨8776580731871324693581511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5851053821247549795721007 8776580731871324693581511)
            ·
              refine ⟨13164871097806987040372267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8776580731871324693581511 13164871097806987040372267)
              ·
                refine ⟨19747306646710480560558401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13164871097806987040372267 19747306646710480560558401)
                ·
                  refine ⟨14810479985032860420418801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19747306646710480560558401 14810479985032860420418801)
                  ·
                    refine ⟨11107859988774645315314101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14810479985032860420418801 11107859988774645315314101)
                    ·
                      refine ⟨1041361873947622998310697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11107859988774645315314101 1041361873947622998310697)
                      ·
                        rfl

theorem cell23_2028045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2028045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028045 prefixEnd_2028045 := by exact prefixLift 2028045
  have htrace : WordTrace (prefixWord ++ tailWord_2028045) baseStart_2028045 baseEnd_2028045 := by
    simpa [prefixWord, tailWord_2028045, baseEnd_2028045] using wordTrace_append hprefix tailTrace_2028045
  have hstable : (prefixWord ++ tailWord_2028045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028045).length < 2 ^ (prefixWord ++ tailWord_2028045).sum := by decide
  have hdescent : baseEnd_2028045 < baseStart_2028045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028072 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_2028072 : Nat := 118140960795 + 2028072 * 2 ^ 59
def prefixEnd_2028072 : Nat := 4983230072969 + 3 ^ 40 * 2028072 * 2
def baseEnd_2028072 : Nat := 1041375737925294392673073

theorem tailTrace_2028072 : CollatzResearch.WordTrace tailWord_2028072 prefixEnd_2028072 1041375737925294392673073 := by
  unfold tailWord_2028072
  simp only [CollatzResearch.WordTrace]
  refine ⟨36984931354324492983507235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49313241805765990644676313 36984931354324492983507235)
  ·
    refine ⟨55477397031486739475260853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36984931354324492983507235 55477397031486739475260853)
    ·
      refine ⟨5201005971701881825805705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55477397031486739475260853 5201005971701881825805705)
      ·
        refine ⟨3900754478776411369354279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5201005971701881825805705 3900754478776411369354279)
        ·
          refine ⟨5851131718164617054031419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3900754478776411369354279 5851131718164617054031419)
          ·
            refine ⟨8776697577246925581047129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5851131718164617054031419 8776697577246925581047129)
            ·
              refine ⟨6582523182935194185785347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8776697577246925581047129 6582523182935194185785347)
              ·
                refine ⟨9873784774402791278678021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582523182935194185785347 9873784774402791278678021)
                ·
                  refine ⟨1851334645200523364752129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9873784774402791278678021 1851334645200523364752129)
                  ·
                    refine ⟨1388500983900392523564097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1851334645200523364752129 1388500983900392523564097)
                    ·
                      refine ⟨1041375737925294392673073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1388500983900392523564097 1041375737925294392673073)
                      ·
                        rfl

theorem cell23_2028072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_2028072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028072 prefixEnd_2028072 := by exact prefixLift 2028072
  have htrace : WordTrace (prefixWord ++ tailWord_2028072) baseStart_2028072 baseEnd_2028072 := by
    simpa [prefixWord, tailWord_2028072, baseEnd_2028072] using wordTrace_append hprefix tailTrace_2028072
  have hstable : (prefixWord ++ tailWord_2028072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028072).length < 2 ^ (prefixWord ++ tailWord_2028072).sum := by decide
  have hdescent : baseEnd_2028072 < baseStart_2028072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028108 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_2028108 : Nat := 118140960795 + 2028108 * 2 ^ 59
def prefixEnd_2028108 : Nat := 4983230072969 + 3 ^ 40 * 2028108 * 2
def baseEnd_2028108 : Nat := 347131407742952083940969

theorem tailTrace_2028108 : CollatzResearch.WordTrace tailWord_2028108 prefixEnd_2028108 347131407742952083940969 := by
  unfold tailWord_2028108
  simp only [CollatzResearch.WordTrace]
  refine ⟨36985587868259282057662489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49314117157679042743549985 36985587868259282057662489)
  ·
    refine ⟨27739190901194461543246867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36985587868259282057662489 27739190901194461543246867)
    ·
      refine ⟨41608786351791692314870301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27739190901194461543246867 41608786351791692314870301)
      ·
        refine ⟨15603294881921884618076363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41608786351791692314870301 15603294881921884618076363)
        ·
          refine ⟨23404942322882826927114545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15603294881921884618076363 23404942322882826927114545)
          ·
            refine ⟨17553706742162120195335909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23404942322882826927114545 17553706742162120195335909)
            ·
              refine ⟨3291320014155397536625483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17553706742162120195335909 3291320014155397536625483)
              ·
                refine ⟨4936980021233096304938225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291320014155397536625483 4936980021233096304938225)
                ·
                  refine ⟨3702735015924822228703669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4936980021233096304938225 3702735015924822228703669)
                  ·
                    refine ⟨347131407742952083940969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3702735015924822228703669 347131407742952083940969)
                    ·
                      rfl

theorem cell23_2028108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_2028108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028108 prefixEnd_2028108 := by exact prefixLift 2028108
  have htrace : WordTrace (prefixWord ++ tailWord_2028108) baseStart_2028108 baseEnd_2028108 := by
    simpa [prefixWord, tailWord_2028108, baseEnd_2028108] using wordTrace_append hprefix tailTrace_2028108
  have hstable : (prefixWord ++ tailWord_2028108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028108).length < 2 ^ (prefixWord ++ tailWord_2028108).sum := by decide
  have hdescent : baseEnd_2028108 < baseStart_2028108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028111 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_2028111 : Nat := 118140960795 + 2028111 * 2 ^ 59
def prefixEnd_2028111 : Nat := 4983230072969 + 3 ^ 40 * 2028111 * 2
def baseEnd_2028111 : Nat := 1041395763670819740085393

theorem tailTrace_2028111 : CollatzResearch.WordTrace tailWord_2028111 prefixEnd_2028111 1041395763670819740085393 := by
  unfold tailWord_2028111
  simp only [CollatzResearch.WordTrace]
  refine ⟨73971285155507695627684187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49314190103671797085122791 73971285155507695627684187)
  ·
    refine ⟨110956927733261543441526281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73971285155507695627684187 110956927733261543441526281)
    ·
      refine ⟨83217695799946157581144711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110956927733261543441526281 83217695799946157581144711)
      ·
        refine ⟨124826543699919236371717067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83217695799946157581144711 124826543699919236371717067)
        ·
          refine ⟨187239815549878854557575601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124826543699919236371717067 187239815549878854557575601)
          ·
            refine ⟨140429861662409140918181701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187239815549878854557575601 140429861662409140918181701)
            ·
              refine ⟨26330599061701713922159069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140429861662409140918181701 26330599061701713922159069)
              ·
                refine ⟨9873974648138142720809651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26330599061701713922159069 9873974648138142720809651)
                ·
                  refine ⟨14810961972207214081214477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9873974648138142720809651 14810961972207214081214477)
                  ·
                    refine ⟨5554110739577705280455429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14810961972207214081214477 5554110739577705280455429)
                    ·
                      refine ⟨1041395763670819740085393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5554110739577705280455429 1041395763670819740085393)
                      ·
                        rfl

theorem cell23_2028111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_2028111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028111 prefixEnd_2028111 := by exact prefixLift 2028111
  have htrace : WordTrace (prefixWord ++ tailWord_2028111) baseStart_2028111 baseEnd_2028111 := by
    simpa [prefixWord, tailWord_2028111, baseEnd_2028111] using wordTrace_append hprefix tailTrace_2028111
  have hstable : (prefixWord ++ tailWord_2028111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028111).length < 2 ^ (prefixWord ++ tailWord_2028111).sum := by decide
  have hdescent : baseEnd_2028111 < baseStart_2028111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028128 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2028128 : Nat := 118140960795 + 2028128 * 2 ^ 59
def prefixEnd_2028128 : Nat := 4983230072969 + 3 ^ 40 * 2028128 * 2
def baseEnd_2028128 : Nat := 1041404492841946173572815

theorem tailTrace_2028128 : CollatzResearch.WordTrace tailWord_2028128 prefixEnd_2028128 1041404492841946173572815 := by
  unfold tailWord_2028128
  simp only [CollatzResearch.WordTrace]
  refine ⟨36985952598223053765526519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49314603464297405020702025 36985952598223053765526519)
  ·
    refine ⟨55478928897334580648289779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36985952598223053765526519 55478928897334580648289779)
    ·
      refine ⟨83218393346001870972434669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55478928897334580648289779 83218393346001870972434669)
      ·
        refine ⟨31206897504750701614663001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83218393346001870972434669 31206897504750701614663001)
        ·
          refine ⟨23405173128563026210997251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31206897504750701614663001 23405173128563026210997251)
          ·
            refine ⟨35107759692844539316495877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23405173128563026210997251 35107759692844539316495877)
            ·
              refine ⟨6582704942408351121842977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35107759692844539316495877 6582704942408351121842977)
              ·
                refine ⟨4937028706806263341382233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6582704942408351121842977 4937028706806263341382233)
                ·
                  refine ⟨3702771530104697506036675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937028706806263341382233 3702771530104697506036675)
                  ·
                    refine ⟨5554157295157046259055013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3702771530104697506036675 5554157295157046259055013)
                    ·
                      refine ⟨1041404492841946173572815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5554157295157046259055013 1041404492841946173572815)
                      ·
                        rfl

theorem cell23_2028128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2028128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028128 prefixEnd_2028128 := by exact prefixLift 2028128
  have htrace : WordTrace (prefixWord ++ tailWord_2028128) baseStart_2028128 baseEnd_2028128 := by
    simpa [prefixWord, tailWord_2028128, baseEnd_2028128] using wordTrace_append hprefix tailTrace_2028128
  have hstable : (prefixWord ++ tailWord_2028128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028128).length < 2 ^ (prefixWord ++ tailWord_2028128).sum := by decide
  have hdescent : baseEnd_2028128 < baseStart_2028128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028131 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2028131 : Nat := 118140960795 + 2028131 * 2 ^ 59
def prefixEnd_2028131 : Nat := 4983230072969 + 3 ^ 40 * 2028131 * 2
def baseEnd_2028131 : Nat := 1041406033283909661835301

theorem tailTrace_2028131 : CollatzResearch.WordTrace tailWord_2028131 prefixEnd_2028131 1041406033283909661835301 := by
  unfold tailWord_2028131
  simp only [CollatzResearch.WordTrace]
  refine ⟨73972014615435239043412247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49314676410290159362274831 73972014615435239043412247)
  ·
    refine ⟨110958021923152858565118371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73972014615435239043412247 110958021923152858565118371)
    ·
      refine ⟨166437032884729287847677557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110958021923152858565118371 166437032884729287847677557)
      ·
        refine ⟨15603471832943370735719771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166437032884729287847677557 15603471832943370735719771)
        ·
          refine ⟨23405207749415056103579657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15603471832943370735719771 23405207749415056103579657)
          ·
            refine ⟨17553905812061292077684743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23405207749415056103579657 17553905812061292077684743)
            ·
              refine ⟨26330858718091938116527115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17553905812061292077684743 26330858718091938116527115)
              ·
                refine ⟨39496288077137907174790673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26330858718091938116527115 39496288077137907174790673)
                ·
                  refine ⟨29622216057853430381093005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39496288077137907174790673 29622216057853430381093005)
                  ·
                    refine ⟨11108331021695036392909877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29622216057853430381093005 11108331021695036392909877)
                    ·
                      refine ⟨1041406033283909661835301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11108331021695036392909877 1041406033283909661835301)
                      ·
                        rfl

theorem cell23_2028131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2028131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028131 prefixEnd_2028131 := by exact prefixLift 2028131
  have htrace : WordTrace (prefixWord ++ tailWord_2028131) baseStart_2028131 baseEnd_2028131 := by
    simpa [prefixWord, tailWord_2028131, baseEnd_2028131] using wordTrace_append hprefix tailTrace_2028131
  have hstable : (prefixWord ++ tailWord_2028131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028131).length < 2 ^ (prefixWord ++ tailWord_2028131).sum := by decide
  have hdescent : baseEnd_2028131 < baseStart_2028131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028165 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_2028165 : Nat := 118140960795 + 2028165 * 2 ^ 59
def prefixEnd_2028165 : Nat := 4983230072969 + 3 ^ 40 * 2028165 * 2
def baseEnd_2028165 : Nat := 1041423491626162528810145

theorem tailTrace_2028165 : CollatzResearch.WordTrace tailWord_2028165 prefixEnd_2028165 1041423491626162528810145 := by
  unfold tailWord_2028165
  simp only [CollatzResearch.WordTrace]
  refine ⟨73973254697312062850149949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49315503131541375233433299 73973254697312062850149949)
  ·
    refine ⟨27739970511492023568806231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73973254697312062850149949 27739970511492023568806231)
    ·
      refine ⟨41609955767238035353209347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27739970511492023568806231 41609955767238035353209347)
      ·
        refine ⟨62414933650857053029814021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41609955767238035353209347 62414933650857053029814021)
        ·
          refine ⟨11702800059535697443090129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62414933650857053029814021 11702800059535697443090129)
          ·
            refine ⟨8777100044651773082317597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11702800059535697443090129 8777100044651773082317597)
            ·
              refine ⟨3291412516744414905869099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8777100044651773082317597 3291412516744414905869099)
              ·
                refine ⟨4937118775116622358803649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291412516744414905869099 4937118775116622358803649)
                ·
                  refine ⟨3702839081337466769102737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937118775116622358803649 3702839081337466769102737)
                  ·
                    refine ⟨2777129311003100076827053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3702839081337466769102737 2777129311003100076827053)
                    ·
                      refine ⟨1041423491626162528810145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2777129311003100076827053 1041423491626162528810145)
                      ·
                        rfl

theorem cell23_2028165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_2028165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028165 prefixEnd_2028165 := by exact prefixLift 2028165
  have htrace : WordTrace (prefixWord ++ tailWord_2028165) baseStart_2028165 baseEnd_2028165 := by
    simpa [prefixWord, tailWord_2028165, baseEnd_2028165] using wordTrace_append hprefix tailTrace_2028165
  have hstable : (prefixWord ++ tailWord_2028165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028165).length < 2 ^ (prefixWord ++ tailWord_2028165).sum := by decide
  have hdescent : baseEnd_2028165 < baseStart_2028165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028188 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2028188 : Nat := 118140960795 + 2028188 * 2 ^ 59
def prefixEnd_2028188 : Nat := 4983230072969 + 3 ^ 40 * 2028188 * 2
def baseEnd_2028188 : Nat := 1041435301681215938822539

theorem tailTrace_2028188 : CollatzResearch.WordTrace tailWord_2028188 prefixEnd_2028188 1041435301681215938822539 := by
  unfold tailWord_2028188
  simp only [CollatzResearch.WordTrace]
  refine ⟨36987046788114368889118609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49316062384152491852158145 36987046788114368889118609)
  ·
    refine ⟨27740285091085776666838957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36987046788114368889118609 27740285091085776666838957)
    ·
      refine ⟨10402606909157166250064609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27740285091085776666838957 10402606909157166250064609)
      ·
        refine ⟨7801955181867874687548457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10402606909157166250064609 7801955181867874687548457)
        ·
          refine ⟨5851466386400906015661343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7801955181867874687548457 5851466386400906015661343)
          ·
            refine ⟨8777199579601359023492015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5851466386400906015661343 8777199579601359023492015)
            ·
              refine ⟨13165799369402038535238023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8777199579601359023492015 13165799369402038535238023)
              ·
                refine ⟨19748699054103057802857035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13165799369402038535238023 19748699054103057802857035)
                ·
                  refine ⟨29623048581154586704285553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19748699054103057802857035 29623048581154586704285553)
                  ·
                    refine ⟨22217286435865940028214165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29623048581154586704285553 22217286435865940028214165)
                    ·
                      refine ⟨1041435301681215938822539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22217286435865940028214165 1041435301681215938822539)
                      ·
                        rfl

theorem cell23_2028188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2028188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028188 prefixEnd_2028188 := by exact prefixLift 2028188
  have htrace : WordTrace (prefixWord ++ tailWord_2028188) baseStart_2028188 baseEnd_2028188 := by
    simpa [prefixWord, tailWord_2028188, baseEnd_2028188] using wordTrace_append hprefix tailTrace_2028188
  have hstable : (prefixWord ++ tailWord_2028188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028188).length < 2 ^ (prefixWord ++ tailWord_2028188).sum := by decide
  have hdescent : baseEnd_2028188 < baseStart_2028188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028222 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_2028222 : Nat := 118140960795 + 2028222 * 2 ^ 59
def prefixEnd_2028222 : Nat := 4983230072969 + 3 ^ 40 * 2028222 * 2
def baseEnd_2028222 : Nat := 1041452760023468805797383

theorem tailTrace_2028222 : CollatzResearch.WordTrace tailWord_2028222 prefixEnd_2028222 1041452760023468805797383 := by
  unfold tailWord_2028222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9246916707263195198121865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49316889105403707723316613 9246916707263195198121865)
  ·
    refine ⟨6935187530447396398591399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9246916707263195198121865 6935187530447396398591399)
    ·
      refine ⟨10402781295671094597887099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6935187530447396398591399 10402781295671094597887099)
      ·
        refine ⟨15604171943506641896830649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10402781295671094597887099 15604171943506641896830649)
        ·
          refine ⟨11703128957629981422622987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15604171943506641896830649 11703128957629981422622987)
          ·
            refine ⟨17554693436444972133934481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11703128957629981422622987 17554693436444972133934481)
            ·
              refine ⟨13166020077333729100450861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17554693436444972133934481 13166020077333729100450861)
              ·
                refine ⟨4937257529000148412669073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13166020077333729100450861 4937257529000148412669073)
                ·
                  refine ⟨3702943146750111309501805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937257529000148412669073 3702943146750111309501805)
                  ·
                    refine ⟨1388603680031291741063177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702943146750111309501805 1388603680031291741063177)
                    ·
                      refine ⟨1041452760023468805797383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1388603680031291741063177 1041452760023468805797383)
                      ·
                        rfl

theorem cell23_2028222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_2028222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028222 prefixEnd_2028222 := by exact prefixLift 2028222
  have htrace : WordTrace (prefixWord ++ tailWord_2028222) baseStart_2028222 baseEnd_2028222 := by
    simpa [prefixWord, tailWord_2028222, baseEnd_2028222] using wordTrace_append hprefix tailTrace_2028222
  have hstable : (prefixWord ++ tailWord_2028222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028222).length < 2 ^ (prefixWord ++ tailWord_2028222).sum := by decide
  have hdescent : baseEnd_2028222 < baseStart_2028222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028248 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2028248 : Nat := 118140960795 + 2028248 * 2 ^ 59
def prefixEnd_2028248 : Nat := 4983230072969 + 3 ^ 40 * 2028248 * 2
def baseEnd_2028248 : Nat := 1041466110520485704072263

theorem tailTrace_2028248 : CollatzResearch.WordTrace tailWord_2028248 prefixEnd_2028248 1041466110520485704072263 := by
  unfold tailWord_2028248
  simp only [CollatzResearch.WordTrace]
  refine ⟨36988140978005684012710699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49317521304007578683614265 36988140978005684012710699)
  ·
    refine ⟨55482211467008526019066049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36988140978005684012710699 55482211467008526019066049)
    ·
      refine ⟨41611658600256394514299537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55482211467008526019066049 41611658600256394514299537)
      ·
        refine ⟨31208743950192295885724653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41611658600256394514299537 31208743950192295885724653)
        ·
          refine ⟨11703278981322110957146745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31208743950192295885724653 11703278981322110957146745)
          ·
            refine ⟨8777459235991583217860059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11703278981322110957146745 8777459235991583217860059)
            ·
              refine ⟨13166188853987374826790089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8777459235991583217860059 13166188853987374826790089)
              ·
                refine ⟨9874641640490531120092567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13166188853987374826790089 9874641640490531120092567)
                ·
                  refine ⟨14811962460735796680138851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9874641640490531120092567 14811962460735796680138851)
                  ·
                    refine ⟨22217943691103695020208277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14811962460735796680138851 22217943691103695020208277)
                    ·
                      refine ⟨1041466110520485704072263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22217943691103695020208277 1041466110520485704072263)
                      ·
                        rfl

theorem cell23_2028248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2028248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028248 prefixEnd_2028248 := by exact prefixLift 2028248
  have htrace : WordTrace (prefixWord ++ tailWord_2028248) baseStart_2028248 baseEnd_2028248 := by
    simpa [prefixWord, tailWord_2028248, baseEnd_2028248] using wordTrace_append hprefix tailTrace_2028248
  have hstable : (prefixWord ++ tailWord_2028248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028248).length < 2 ^ (prefixWord ++ tailWord_2028248).sum := by decide
  have hdescent : baseEnd_2028248 < baseStart_2028248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028285 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_2028285 : Nat := 118140960795 + 2028285 * 2 ^ 59
def prefixEnd_2028285 : Nat := 4983230072969 + 3 ^ 40 * 2028285 * 2
def baseEnd_2028285 : Nat := 1041485109304702059309593

theorem tailTrace_2028285 : CollatzResearch.WordTrace tailWord_2028285 prefixEnd_2028285 1041485109304702059309593 := by
  unfold tailWord_2028285
  simp only [CollatzResearch.WordTrace]
  refine ⟨73977631456877323344518309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49318420971251548896345539 73977631456877323344518309)
  ·
    refine ⟨13870805898164498127097183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73977631456877323344518309 13870805898164498127097183)
    ·
      refine ⟨20806208847246747190645775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13870805898164498127097183 20806208847246747190645775)
      ·
        refine ⟨31209313270870120785968663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20806208847246747190645775 31209313270870120785968663)
        ·
          refine ⟨46813969906305181178952995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31209313270870120785968663 46813969906305181178952995)
          ·
            refine ⟨70220954859457771768429493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46813969906305181178952995 70220954859457771768429493)
            ·
              refine ⟨6583214518074166103290265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70220954859457771768429493 6583214518074166103290265)
              ·
                refine ⟨4937410888555624577467699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6583214518074166103290265 4937410888555624577467699)
                ·
                  refine ⟨7406116332833436866201549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937410888555624577467699 7406116332833436866201549)
                  ·
                    refine ⟨2777293624812538824825581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7406116332833436866201549 2777293624812538824825581)
                    ·
                      refine ⟨1041485109304702059309593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2777293624812538824825581 1041485109304702059309593)
                      ·
                        rfl

theorem cell23_2028285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_2028285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028285 prefixEnd_2028285 := by exact prefixLift 2028285
  have htrace : WordTrace (prefixWord ++ tailWord_2028285) baseStart_2028285 baseEnd_2028285 := by
    simpa [prefixWord, tailWord_2028285, baseEnd_2028285] using wordTrace_append hprefix tailTrace_2028285
  have hstable : (prefixWord ++ tailWord_2028285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028285).length < 2 ^ (prefixWord ++ tailWord_2028285).sum := by decide
  have hdescent : baseEnd_2028285 < baseStart_2028285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028348 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 11]
def baseStart_2028348 : Nat := 118140960795 + 2028348 * 2 ^ 59
def prefixEnd_2028348 : Nat := 4983230072969 + 3 ^ 40 * 2028348 * 2
def baseEnd_2028348 : Nat := 115724162065103923646867

theorem tailTrace_2028348 : CollatzResearch.WordTrace tailWord_2028348 prefixEnd_2028348 115724162065103923646867 := by
  unfold tailWord_2028348
  simp only [CollatzResearch.WordTrace]
  refine ⟨36989964627824542552030849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49319952837099390069374465 36989964627824542552030849)
  ·
    refine ⟨27742473470868406914023137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36989964627824542552030849 27742473470868406914023137)
    ·
      refine ⟨20806855103151305185517353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27742473470868406914023137 20806855103151305185517353)
      ·
        refine ⟨15605141327363478889138015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20806855103151305185517353 15605141327363478889138015)
        ·
          refine ⟨23407711991045218333707023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15605141327363478889138015 23407711991045218333707023)
          ·
            refine ⟨35111567986567827500560535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23407711991045218333707023 35111567986567827500560535)
            ·
              refine ⟨52667351979851741250840803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35111567986567827500560535 52667351979851741250840803)
              ·
                refine ⟨79001027969777611876261205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52667351979851741250840803 79001027969777611876261205)
                ·
                  refine ⟨115724162065103923646867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 79001027969777611876261205 115724162065103923646867)
                  ·
                    rfl

theorem cell23_2028348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_2028348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028348 prefixEnd_2028348 := by exact prefixLift 2028348
  have htrace : WordTrace (prefixWord ++ tailWord_2028348) baseStart_2028348 baseEnd_2028348 := by
    simpa [prefixWord, tailWord_2028348, baseEnd_2028348] using wordTrace_append hprefix tailTrace_2028348
  have hstable : (prefixWord ++ tailWord_2028348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028348).length < 2 ^ (prefixWord ++ tailWord_2028348).sum := by decide
  have hdescent : baseEnd_2028348 < baseStart_2028348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028353 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2028353 : Nat := 118140960795 + 2028353 * 2 ^ 59
def prefixEnd_2028353 : Nat := 4983230072969 + 3 ^ 40 * 2028353 * 2
def baseEnd_2028353 : Nat := 1041520025989207793259281

theorem tailTrace_2028353 : CollatzResearch.WordTrace tailWord_2028353 prefixEnd_2028353 1041520025989207793259281 := by
  unfold tailWord_2028353
  simp only [CollatzResearch.WordTrace]
  refine ⟨73980111620630970957993713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49320074413753980638662475 73980111620630970957993713)
  ·
    refine ⟨55485083715473228218495285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73980111620630970957993713 55485083715473228218495285)
    ·
      refine ⟨5201726598325615145483933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55485083715473228218495285 5201726598325615145483933)
      ·
        refine ⟨1950647474372105679556475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5201726598325615145483933 1950647474372105679556475)
        ·
          refine ⟨2925971211558158519334713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950647474372105679556475 2925971211558158519334713)
          ·
            refine ⟨2194478408668618889501035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2925971211558158519334713 2194478408668618889501035)
            ·
              refine ⟨3291717613002928334251553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2194478408668618889501035 3291717613002928334251553)
              ·
                refine ⟨2468788209752196250688665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3291717613002928334251553 2468788209752196250688665)
                ·
                  refine ⟨1851591157314147188016499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2468788209752196250688665 1851591157314147188016499)
                  ·
                    refine ⟨2777386735971220782024749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1851591157314147188016499 2777386735971220782024749)
                    ·
                      refine ⟨1041520025989207793259281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2777386735971220782024749 1041520025989207793259281)
                      ·
                        rfl

theorem cell23_2028353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2028353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028353 prefixEnd_2028353 := by exact prefixLift 2028353
  have htrace : WordTrace (prefixWord ++ tailWord_2028353) baseStart_2028353 baseEnd_2028353 := by
    simpa [prefixWord, tailWord_2028353, baseEnd_2028353] using wordTrace_append hprefix tailTrace_2028353
  have hstable : (prefixWord ++ tailWord_2028353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028353).length < 2 ^ (prefixWord ++ tailWord_2028353).sum := by decide
  have hdescent : baseEnd_2028353 < baseStart_2028353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028415 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_2028415 : Nat := 118140960795 + 2028415 * 2 ^ 59
def prefixEnd_2028415 : Nat := 4983230072969 + 3 ^ 40 * 2028415 * 2
def baseEnd_2028415 : Nat := 1041551861789786550683995

theorem tailTrace_2028415 : CollatzResearch.WordTrace tailWord_2028415 prefixEnd_2028415 1041551861789786550683995 := by
  unfold tailWord_2028415
  simp only [CollatzResearch.WordTrace]
  refine ⟨73982372946406355546750699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49321581964270903697833799 73982372946406355546750699)
  ·
    refine ⟨110973559419609533320126049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73982372946406355546750699 110973559419609533320126049)
    ·
      refine ⟨83230169564707149990094537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110973559419609533320126049 83230169564707149990094537)
      ·
        refine ⟨62422627173530362492570903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83230169564707149990094537 62422627173530362492570903)
        ·
          refine ⟨93633940760295543738856355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62422627173530362492570903 93633940760295543738856355)
          ·
            refine ⟨140450911140443315608284533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93633940760295543738856355 140450911140443315608284533)
            ·
              refine ⟨13167272919416560838276675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140450911140443315608284533 13167272919416560838276675)
              ·
                refine ⟨19750909379124841257415013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167272919416560838276675 19750909379124841257415013)
                ·
                  refine ⟨3703295508585907735765315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19750909379124841257415013 3703295508585907735765315)
                  ·
                    refine ⟨5554943262878861603647973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703295508585907735765315 5554943262878861603647973)
                    ·
                      refine ⟨1041551861789786550683995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5554943262878861603647973 1041551861789786550683995)
                      ·
                        rfl

theorem cell23_2028415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_2028415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028415 prefixEnd_2028415 := by exact prefixLift 2028415
  have htrace : WordTrace (prefixWord ++ tailWord_2028415) baseStart_2028415 baseEnd_2028415 := by
    simpa [prefixWord, tailWord_2028415, baseEnd_2028415] using wordTrace_append hprefix tailTrace_2028415
  have hstable : (prefixWord ++ tailWord_2028415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028415).length < 2 ^ (prefixWord ++ tailWord_2028415).sum := by decide
  have hdescent : baseEnd_2028415 < baseStart_2028415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028435 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 3]
def baseStart_2028435 : Nat := 118140960795 + 2028435 * 2 ^ 59
def prefixEnd_2028435 : Nat := 4983230072969 + 3 ^ 40 * 2028435 * 2
def baseEnd_2028435 : Nat := 1041562131402876472433903

theorem tailTrace_2028435 : CollatzResearch.WordTrace tailWord_2028435 prefixEnd_2028435 1041562131402876472433903 := by
  unfold tailWord_2028435
  simp only [CollatzResearch.WordTrace]
  refine ⟨73983102406333898962478759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49322068270889265974985839 73983102406333898962478759)
  ·
    refine ⟨110974653609500848443718139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73983102406333898962478759 110974653609500848443718139)
    ·
      refine ⟨166461980414251272665577209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110974653609500848443718139 166461980414251272665577209)
      ·
        refine ⟨124846485310688454499182907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166461980414251272665577209 124846485310688454499182907)
        ·
          refine ⟨187269727966032681748774361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124846485310688454499182907 187269727966032681748774361)
          ·
            refine ⟨140452295974524511311580771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187269727966032681748774361 140452295974524511311580771)
            ·
              refine ⟨210678443961786766967371157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140452295974524511311580771 210678443961786766967371157)
              ·
                refine ⟨9875552060708754701595523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 210678443961786766967371157 9875552060708754701595523)
                ·
                  refine ⟨14813328091063132052393285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9875552060708754701595523 14813328091063132052393285)
                  ·
                    refine ⟨2777499017074337259823741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14813328091063132052393285 2777499017074337259823741)
                    ·
                      refine ⟨1041562131402876472433903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2777499017074337259823741 1041562131402876472433903)
                      ·
                        rfl

theorem cell23_2028435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_2028435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028435 prefixEnd_2028435 := by exact prefixLift 2028435
  have htrace : WordTrace (prefixWord ++ tailWord_2028435) baseStart_2028435 baseEnd_2028435 := by
    simpa [prefixWord, tailWord_2028435, baseEnd_2028435] using wordTrace_append hprefix tailTrace_2028435
  have hstable : (prefixWord ++ tailWord_2028435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028435).length < 2 ^ (prefixWord ++ tailWord_2028435).sum := by decide
  have hdescent : baseEnd_2028435 < baseStart_2028435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028449 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2028449 : Nat := 118140960795 + 2028449 * 2 ^ 59
def prefixEnd_2028449 : Nat := 4983230072969 + 3 ^ 40 * 2028449 * 2
def baseEnd_2028449 : Nat := 1041569320132039417658839

theorem tailTrace_2028449 : CollatzResearch.WordTrace tailWord_2028449 prefixEnd_2028449 1041569320132039417658839 := by
  unfold tailWord_2028449
  simp only [CollatzResearch.WordTrace]
  refine ⟨73983613028283179353488401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49322408685522119568992267 73983613028283179353488401)
  ·
    refine ⟨55487709771212384515116301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73983613028283179353488401 55487709771212384515116301)
    ·
      refine ⟨20807891164204644193168613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55487709771212384515116301 20807891164204644193168613)
      ·
        refine ⟨3901479593288370786219115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20807891164204644193168613 3901479593288370786219115)
        ·
          refine ⟨5852219389932556179328673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901479593288370786219115 5852219389932556179328673)
          ·
            refine ⟨4389164542449417134496505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852219389932556179328673 4389164542449417134496505)
            ·
              refine ⟨3291873406837062850872379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389164542449417134496505 3291873406837062850872379)
              ·
                refine ⟨4937810110255594276308569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291873406837062850872379 4937810110255594276308569)
                ·
                  refine ⟨3703357582691695707231427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937810110255594276308569 3703357582691695707231427)
                  ·
                    refine ⟨5555036374037543560847141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3703357582691695707231427 5555036374037543560847141)
                    ·
                      refine ⟨1041569320132039417658839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5555036374037543560847141 1041569320132039417658839)
                      ·
                        rfl

theorem cell23_2028449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2028449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028449 prefixEnd_2028449 := by exact prefixLift 2028449
  have htrace : WordTrace (prefixWord ++ tailWord_2028449) baseStart_2028449 baseEnd_2028449 := by
    simpa [prefixWord, tailWord_2028449, baseEnd_2028449] using wordTrace_append hprefix tailTrace_2028449
  have hstable : (prefixWord ++ tailWord_2028449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028449).length < 2 ^ (prefixWord ++ tailWord_2028449).sum := by decide
  have hdescent : baseEnd_2028449 < baseStart_2028449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028472 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 6]
def baseStart_2028472 : Nat := 118140960795 + 2028472 * 2 ^ 59
def prefixEnd_2028472 : Nat := 4983230072969 + 3 ^ 40 * 2028472 * 2
def baseEnd_2028472 : Nat := 115731236687454758630137

theorem tailTrace_2028472 : CollatzResearch.WordTrace tailWord_2028472 prefixEnd_2028472 115731236687454758630137 := by
  unfold tailWord_2028472
  simp only [CollatzResearch.WordTrace]
  refine ⟨36992225953599927140787835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49322967938133236187717113 36992225953599927140787835)
  ·
    refine ⟨55488338930399890711181753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36992225953599927140787835 55488338930399890711181753)
    ·
      refine ⟨41616254197799918033386315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55488338930399890711181753 41616254197799918033386315)
      ·
        refine ⟨62424381296699877050079473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41616254197799918033386315 62424381296699877050079473)
        ·
          refine ⟨46818285972524907787559605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62424381296699877050079473 46818285972524907787559605)
          ·
            refine ⟨4389214309924210105083713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46818285972524907787559605 4389214309924210105083713)
            ·
              refine ⟨3291910732443157578812785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389214309924210105083713 3291910732443157578812785)
              ·
                refine ⟨2468933049332368184109589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3291910732443157578812785 2468933049332368184109589)
                ·
                  refine ⟨115731236687454758630137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2468933049332368184109589 115731236687454758630137)
                  ·
                    rfl

theorem cell23_2028472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 6].length) (baseStart_2028472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028472 prefixEnd_2028472 := by exact prefixLift 2028472
  have htrace : WordTrace (prefixWord ++ tailWord_2028472) baseStart_2028472 baseEnd_2028472 := by
    simpa [prefixWord, tailWord_2028472, baseEnd_2028472] using wordTrace_append hprefix tailTrace_2028472
  have hstable : (prefixWord ++ tailWord_2028472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028472).length < 2 ^ (prefixWord ++ tailWord_2028472).sum := by decide
  have hdescent : baseEnd_2028472 < baseStart_2028472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028519 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 1, 5]
def baseStart_2028519 : Nat := 118140960795 + 2028519 * 2 ^ 59
def prefixEnd_2028519 : Nat := 4983230072969 + 3 ^ 40 * 2028519 * 2
def baseEnd_2028519 : Nat := 347201754592618047927839

theorem tailTrace_2028519 : CollatzResearch.WordTrace tailWord_2028519 prefixEnd_2028519 347201754592618047927839 := by
  unfold tailWord_2028519
  simp only [CollatzResearch.WordTrace]
  refine ⟨73986166138029581308536611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49324110758686387539024407 73986166138029581308536611)
  ·
    refine ⟨110979249207044371962804917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73986166138029581308536611 110979249207044371962804917)
    ·
      refine ⟨10404304613160409871512961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110979249207044371962804917 10404304613160409871512961)
      ·
        refine ⟨7803228459870307403634721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10404304613160409871512961 7803228459870307403634721)
        ·
          refine ⟨5852421344902730552726041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7803228459870307403634721 5852421344902730552726041)
          ·
            refine ⟨4389316008677047914544531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852421344902730552726041 4389316008677047914544531)
            ·
              refine ⟨6583974013015571871816797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389316008677047914544531 6583974013015571871816797)
              ·
                refine ⟨2468990254880839451931299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6583974013015571871816797 2468990254880839451931299)
                ·
                  refine ⟨3703485382321259177896949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468990254880839451931299 3703485382321259177896949)
                  ·
                    refine ⟨347201754592618047927839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3703485382321259177896949 347201754592618047927839)
                    ·
                      rfl

theorem cell23_2028519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_2028519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028519 prefixEnd_2028519 := by exact prefixLift 2028519
  have htrace : WordTrace (prefixWord ++ tailWord_2028519) baseStart_2028519 baseEnd_2028519 := by
    simpa [prefixWord, tailWord_2028519, baseEnd_2028519] using wordTrace_append hprefix tailTrace_2028519
  have hstable : (prefixWord ++ tailWord_2028519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028519).length < 2 ^ (prefixWord ++ tailWord_2028519).sum := by decide
  have hdescent : baseEnd_2028519 < baseStart_2028519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028535 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_2028535 : Nat := 118140960795 + 2028535 * 2 ^ 59
def prefixEnd_2028535 : Nat := 4983230072969 + 3 ^ 40 * 2028535 * 2
def baseEnd_2028535 : Nat := 1041613479468326081183443

theorem tailTrace_2028535 : CollatzResearch.WordTrace tailWord_2028535 prefixEnd_2028535 1041613479468326081183443 := by
  unfold tailWord_2028535
  simp only [CollatzResearch.WordTrace]
  refine ⟨73986749705971616041119059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49324499803981077360746039 73986749705971616041119059)
  ·
    refine ⟨110980124558957424061678589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73986749705971616041119059 110980124558957424061678589)
    ·
      refine ⟨41617546709609034023129471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110980124558957424061678589 41617546709609034023129471)
      ·
        refine ⟨62426320064413551034694207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41617546709609034023129471 62426320064413551034694207)
        ·
          refine ⟨93639480096620326552041311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62426320064413551034694207 93639480096620326552041311)
          ·
            refine ⟨140459220144930489828061967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93639480096620326552041311 140459220144930489828061967)
            ·
              refine ⟨210688830217395734742092951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140459220144930489828061967 210688830217395734742092951)
              ·
                refine ⟨316033245326093602113139427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210688830217395734742092951 316033245326093602113139427)
                ·
                  refine ⟨474049867989140403169709141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316033245326093602113139427 474049867989140403169709141)
                  ·
                    refine ⟨5555271890497739099645029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 474049867989140403169709141 5555271890497739099645029)
                    ·
                      refine ⟨1041613479468326081183443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5555271890497739099645029 1041613479468326081183443)
                      ·
                        rfl

theorem cell23_2028535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_2028535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028535 prefixEnd_2028535 := by exact prefixLift 2028535
  have htrace : WordTrace (prefixWord ++ tailWord_2028535) baseStart_2028535 baseEnd_2028535 := by
    simpa [prefixWord, tailWord_2028535, baseEnd_2028535] using wordTrace_append hprefix tailTrace_2028535
  have hstable : (prefixWord ++ tailWord_2028535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028535).length < 2 ^ (prefixWord ++ tailWord_2028535).sum := by decide
  have hdescent : baseEnd_2028535 < baseStart_2028535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028552 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2028552 : Nat := 118140960795 + 2028552 * 2 ^ 59
def prefixEnd_2028552 : Nat := 4983230072969 + 3 ^ 40 * 2028552 * 2
def baseEnd_2028552 : Nat := 1041622208639452514670865

theorem tailTrace_2028552 : CollatzResearch.WordTrace tailWord_2028552 prefixEnd_2028552 1041622208639452514670865 := by
  unfold tailWord_2028552
  simp only [CollatzResearch.WordTrace]
  refine ⟨36993684873455013972243955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49324913164606685296325273 36993684873455013972243955)
  ·
    refine ⟨55490527310182520958365933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36993684873455013972243955 55490527310182520958365933)
    ·
      refine ⟨20808947741318445359387225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55490527310182520958365933 20808947741318445359387225)
      ·
        refine ⟨15606710805988834019540419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20808947741318445359387225 15606710805988834019540419)
        ·
          refine ⟨23410066208983251029310629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15606710805988834019540419 23410066208983251029310629)
          ·
            refine ⟨4389387414184359567995743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23410066208983251029310629 4389387414184359567995743)
            ·
              refine ⟨6584081121276539351993615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389387414184359567995743 6584081121276539351993615)
              ·
                refine ⟨9876121681914809027990423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584081121276539351993615 9876121681914809027990423)
                ·
                  refine ⟨14814182522872213541985635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876121681914809027990423 14814182522872213541985635)
                  ·
                    refine ⟨22221273784308320312978453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14814182522872213541985635 22221273784308320312978453)
                    ·
                      refine ⟨1041622208639452514670865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22221273784308320312978453 1041622208639452514670865)
                      ·
                        rfl

theorem cell23_2028552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2028552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028552 prefixEnd_2028552 := by exact prefixLift 2028552
  have htrace : WordTrace (prefixWord ++ tailWord_2028552) baseStart_2028552 baseEnd_2028552 := by
    simpa [prefixWord, tailWord_2028552, baseEnd_2028552] using wordTrace_append hprefix tailTrace_2028552
  have hstable : (prefixWord ++ tailWord_2028552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028552).length < 2 ^ (prefixWord ++ tailWord_2028552).sum := by decide
  have hdescent : baseEnd_2028552 < baseStart_2028552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028556 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 3, 2, 2]
def baseStart_2028556 : Nat := 118140960795 + 2028556 * 2 ^ 59
def prefixEnd_2028556 : Nat := 4983230072969 + 3 ^ 40 * 2028556 * 2
def baseEnd_2028556 : Nat := 1041624262562070499020847

theorem tailTrace_2028556 : CollatzResearch.WordTrace tailWord_2028556 prefixEnd_2028556 1041624262562070499020847 := by
  unfold tailWord_2028556
  simp only [CollatzResearch.WordTrace]
  refine ⟨36993757819447768313816761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49325010425930357751755681 36993757819447768313816761)
  ·
    refine ⟨27745318364585826235362571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36993757819447768313816761 27745318364585826235362571)
    ·
      refine ⟨41617977546878739353043857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27745318364585826235362571 41617977546878739353043857)
      ·
        refine ⟨31213483160159054514782893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41617977546878739353043857 31213483160159054514782893)
        ·
          refine ⟨11705056185059645443043585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31213483160159054514782893 11705056185059645443043585)
          ·
            refine ⟨8778792138794734082282689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11705056185059645443043585 8778792138794734082282689)
            ·
              refine ⟨6584094104096050561712017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778792138794734082282689 6584094104096050561712017)
              ·
                refine ⟨4938070578072037921284013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6584094104096050561712017 4938070578072037921284013)
                ·
                  refine ⟨1851776466777014220481505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4938070578072037921284013 1851776466777014220481505)
                  ·
                    refine ⟨1388832350082760665361129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1851776466777014220481505 1388832350082760665361129)
                    ·
                      refine ⟨1041624262562070499020847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1388832350082760665361129 1041624262562070499020847)
                      ·
                        rfl

theorem cell23_2028556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_2028556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028556 prefixEnd_2028556 := by exact prefixLift 2028556
  have htrace : WordTrace (prefixWord ++ tailWord_2028556) baseStart_2028556 baseEnd_2028556 := by
    simpa [prefixWord, tailWord_2028556, baseEnd_2028556] using wordTrace_append hprefix tailTrace_2028556
  have hstable : (prefixWord ++ tailWord_2028556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028556).length < 2 ^ (prefixWord ++ tailWord_2028556).sum := by decide
  have hdescent : baseEnd_2028556 < baseStart_2028556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028576 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2028576 : Nat := 118140960795 + 2028576 * 2 ^ 59
def prefixEnd_2028576 : Nat := 4983230072969 + 3 ^ 40 * 2028576 * 2
def baseEnd_2028576 : Nat := 1041634532175160420770755

theorem tailTrace_2028576 : CollatzResearch.WordTrace tailWord_2028576 prefixEnd_2028576 1041634532175160420770755 := by
  unfold tailWord_2028576
  simp only [CollatzResearch.WordTrace]
  refine ⟨36994122549411540021680791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49325496732548720028907721 36994122549411540021680791)
  ·
    refine ⟨55491183824117310032521187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36994122549411540021680791 55491183824117310032521187)
    ·
      refine ⟨83236775736175965048781781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55491183824117310032521187 83236775736175965048781781)
      ·
        refine ⟨1950861931316624180830823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 83236775736175965048781781 1950861931316624180830823)
        ·
          refine ⟨2926292896974936271246235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950861931316624180830823 2926292896974936271246235)
          ·
            refine ⟨4389439345462404406869353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926292896974936271246235 4389439345462404406869353)
            ·
              refine ⟨3292079509096803305152015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389439345462404406869353 3292079509096803305152015)
              ·
                refine ⟨4938119263645204957728023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292079509096803305152015 4938119263645204957728023)
                ·
                  refine ⟨7407178895467807436592035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938119263645204957728023 7407178895467807436592035)
                  ·
                    refine ⟨11110768343201711154888053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7407178895467807436592035 11110768343201711154888053)
                    ·
                      refine ⟨1041634532175160420770755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11110768343201711154888053 1041634532175160420770755)
                      ·
                        rfl

theorem cell23_2028576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2028576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028576 prefixEnd_2028576 := by exact prefixLift 2028576
  have htrace : WordTrace (prefixWord ++ tailWord_2028576) baseStart_2028576 baseEnd_2028576 := by
    simpa [prefixWord, tailWord_2028576, baseEnd_2028576] using wordTrace_append hprefix tailTrace_2028576
  have hstable : (prefixWord ++ tailWord_2028576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028576).length < 2 ^ (prefixWord ++ tailWord_2028576).sum := by decide
  have hdescent : baseEnd_2028576 < baseStart_2028576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028599 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 3, 3, 2]
def baseStart_2028599 : Nat := 118140960795 + 2028599 * 2 ^ 59
def prefixEnd_2028599 : Nat := 4983230072969 + 3 ^ 40 * 2028599 * 2
def baseEnd_2028599 : Nat := 1041646342230213830783149

theorem tailTrace_2028599 : CollatzResearch.WordTrace tailWord_2028599 prefixEnd_2028599 1041646342230213830783149 := by
  unfold tailWord_2028599
  simp only [CollatzResearch.WordTrace]
  refine ⟨73989083977739754971448851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49326055985159836647632567 73989083977739754971448851)
  ·
    refine ⟨110983625966609632457173277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73989083977739754971448851 110983625966609632457173277)
    ·
      refine ⟨41618859737478612171439979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110983625966609632457173277 41618859737478612171439979)
      ·
        refine ⟨62428289606217918257159969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41618859737478612171439979 62428289606217918257159969)
        ·
          refine ⟨46821217204663438692869977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62428289606217918257159969 46821217204663438692869977)
          ·
            refine ⟨35115912903497579019652483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46821217204663438692869977 35115912903497579019652483)
            ·
              refine ⟨52673869355246368529478725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35115912903497579019652483 52673869355246368529478725)
              ·
                refine ⟨9876350504108694099277261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52673869355246368529478725 9876350504108694099277261)
                ·
                  refine ⟨3703631439040760287228973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9876350504108694099277261 3703631439040760287228973)
                  ·
                    refine ⟨1388861789640285107710865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703631439040760287228973 1388861789640285107710865)
                    ·
                      refine ⟨1041646342230213830783149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1388861789640285107710865 1041646342230213830783149)
                      ·
                        rfl

theorem cell23_2028599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_2028599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028599 prefixEnd_2028599 := by exact prefixLift 2028599
  have htrace : WordTrace (prefixWord ++ tailWord_2028599) baseStart_2028599 baseEnd_2028599 := by
    simpa [prefixWord, tailWord_2028599, baseEnd_2028599] using wordTrace_append hprefix tailTrace_2028599
  have hstable : (prefixWord ++ tailWord_2028599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028599).length < 2 ^ (prefixWord ++ tailWord_2028599).sum := by decide
  have hdescent : baseEnd_2028599 < baseStart_2028599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028632 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2028632 : Nat := 118140960795 + 2028632 * 2 ^ 59
def prefixEnd_2028632 : Nat := 4983230072969 + 3 ^ 40 * 2028632 * 2
def baseEnd_2028632 : Nat := 1041663287091812201670497

theorem tailTrace_2028632 : CollatzResearch.WordTrace tailWord_2028632 prefixEnd_2028632 1041663287091812201670497 := by
  unfold tailWord_2028632
  simp only [CollatzResearch.WordTrace]
  refine ⟨36995143793310100803700075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49326858391080134404933433 36995143793310100803700075)
  ·
    refine ⟨55492715689965151205550113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36995143793310100803700075 55492715689965151205550113)
    ·
      refine ⟨41619536767473863404162585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55492715689965151205550113 41619536767473863404162585)
      ·
        refine ⟨31214652575605397553121939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41619536767473863404162585 31214652575605397553121939)
        ·
          refine ⟨46821978863408096329682909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31214652575605397553121939 46821978863408096329682909)
          ·
            refine ⟨17558242073778036123631091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46821978863408096329682909 17558242073778036123631091)
            ·
              refine ⟨26337363110667054185446637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17558242073778036123631091 26337363110667054185446637)
              ·
                refine ⟨9876511166500145319542489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26337363110667054185446637 9876511166500145319542489)
                ·
                  refine ⟨7407383374875108989656867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9876511166500145319542489 7407383374875108989656867)
                  ·
                    refine ⟨11111075062312663484485301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7407383374875108989656867 11111075062312663484485301)
                    ·
                      refine ⟨1041663287091812201670497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11111075062312663484485301 1041663287091812201670497)
                      ·
                        rfl

theorem cell23_2028632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2028632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028632 prefixEnd_2028632 := by exact prefixLift 2028632
  have htrace : WordTrace (prefixWord ++ tailWord_2028632) baseStart_2028632 baseEnd_2028632 := by
    simpa [prefixWord, tailWord_2028632, baseEnd_2028632] using wordTrace_append hprefix tailTrace_2028632
  have hstable : (prefixWord ++ tailWord_2028632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028632).length < 2 ^ (prefixWord ++ tailWord_2028632).sum := by decide
  have hdescent : baseEnd_2028632 < baseStart_2028632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028652 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 7]
def baseStart_2028652 : Nat := 118140960795 + 2028652 * 2 ^ 59
def prefixEnd_2028652 : Nat := 4983230072969 + 3 ^ 40 * 2028652 * 2
def baseEnd_2028652 : Nat := 115741506300544680380045

theorem tailTrace_2028652 : CollatzResearch.WordTrace tailWord_2028652 prefixEnd_2028652 115741506300544680380045 := by
  unfold tailWord_2028652
  simp only [CollatzResearch.WordTrace]
  refine ⟨36995508523273872511564105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49327344697698496682085473 36995508523273872511564105)
  ·
    refine ⟨27746631392455404383673079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36995508523273872511564105 27746631392455404383673079)
    ·
      refine ⟨41619947088683106575509619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27746631392455404383673079 41619947088683106575509619)
      ·
        refine ⟨62429920633024659863264429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41619947088683106575509619 62429920633024659863264429)
        ·
          refine ⟨23411220237384247448724161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62429920633024659863264429 23411220237384247448724161)
          ·
            refine ⟨17558415178038185586543121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23411220237384247448724161 17558415178038185586543121)
            ·
              refine ⟨13168811383528639189907341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17558415178038185586543121 13168811383528639189907341)
              ·
                refine ⟨4938304268823239696215253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13168811383528639189907341 4938304268823239696215253)
                ·
                  refine ⟨115741506300544680380045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4938304268823239696215253 115741506300544680380045)
                  ·
                    rfl

theorem cell23_2028652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_2028652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028652 prefixEnd_2028652 := by exact prefixLift 2028652
  have htrace : WordTrace (prefixWord ++ tailWord_2028652) baseStart_2028652 baseEnd_2028652 := by
    simpa [prefixWord, tailWord_2028652, baseEnd_2028652] using wordTrace_append hprefix tailTrace_2028652
  have hstable : (prefixWord ++ tailWord_2028652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028652).length < 2 ^ (prefixWord ++ tailWord_2028652).sum := by decide
  have hdescent : baseEnd_2028652 < baseStart_2028652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028686 : List Nat := [4, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_2028686 : Nat := 118140960795 + 2028686 * 2 ^ 59
def prefixEnd_2028686 : Nat := 4983230072969 + 3 ^ 40 * 2028686 * 2
def baseEnd_2028686 : Nat := 115743446116350554488361

theorem tailTrace_2028686 : CollatzResearch.WordTrace tailWord_2028686 prefixEnd_2028686 115743446116350554488361 := by
  unfold tailWord_2028686
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249032141053071103733239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49328171418949712553243941 9249032141053071103733239)
  ·
    refine ⟨13873548211579606655599859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9249032141053071103733239 13873548211579606655599859)
    ·
      refine ⟨20810322317369409983399789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13873548211579606655599859 20810322317369409983399789)
      ·
        refine ⟨7803870869013528743774921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20810322317369409983399789 7803870869013528743774921)
        ·
          refine ⟨5852903151760146557831191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7803870869013528743774921 5852903151760146557831191)
          ·
            refine ⟨8779354727640219836746787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852903151760146557831191 8779354727640219836746787)
            ·
              refine ⟨13169032091460329755120181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779354727640219836746787 13169032091460329755120181)
              ·
                refine ⟨1234596758574405914542517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13169032091460329755120181 1234596758574405914542517)
                ·
                  refine ⟨115743446116350554488361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1234596758574405914542517 115743446116350554488361)
                  ·
                    rfl

theorem cell23_2028686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_2028686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028686 prefixEnd_2028686 := by exact prefixLift 2028686
  have htrace : WordTrace (prefixWord ++ tailWord_2028686) baseStart_2028686 baseEnd_2028686 := by
    simpa [prefixWord, tailWord_2028686, baseEnd_2028686] using wordTrace_append hprefix tailTrace_2028686
  have hstable : (prefixWord ++ tailWord_2028686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028686).length < 2 ^ (prefixWord ++ tailWord_2028686).sum := by decide
  have hdescent : baseEnd_2028686 < baseStart_2028686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028826 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_2028826 : Nat := 118140960795 + 2028826 * 2 ^ 59
def prefixEnd_2028826 : Nat := 4983230072969 + 3 ^ 40 * 2028826 * 2
def baseEnd_2028826 : Nat := 1041762902338784442644605

theorem tailTrace_2028826 : CollatzResearch.WordTrace tailWord_2028826 prefixEnd_2028826 1041762902338784442644605 := by
  unfold tailWord_2028826
  simp only [CollatzResearch.WordTrace]
  refine ⟨18499340836979343184990583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49331575565278248493308221 18499340836979343184990583)
  ·
    refine ⟨27749011255469014777485875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18499340836979343184990583 27749011255469014777485875)
    ·
      refine ⟨41623516883203522166228813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27749011255469014777485875 41623516883203522166228813)
      ·
        refine ⟨15608818831201320812335805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41623516883203522166228813 15608818831201320812335805)
        ·
          refine ⟨5853307061700495304625927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15608818831201320812335805 5853307061700495304625927)
          ·
            refine ⟨8779960592550742956938891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5853307061700495304625927 8779960592550742956938891)
            ·
              refine ⟨13169940888826114435408337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779960592550742956938891 13169940888826114435408337)
              ·
                refine ⟨9877455666619585826556253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13169940888826114435408337 9877455666619585826556253)
                ·
                  refine ⟨3704045874982344684958595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9877455666619585826556253 3704045874982344684958595)
                  ·
                    refine ⟨5556068812473517027437893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704045874982344684958595 5556068812473517027437893)
                    ·
                      refine ⟨1041762902338784442644605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5556068812473517027437893 1041762902338784442644605)
                      ·
                        rfl

theorem cell23_2028826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_2028826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028826 prefixEnd_2028826 := by exact prefixLift 2028826
  have htrace : WordTrace (prefixWord ++ tailWord_2028826) baseStart_2028826 baseEnd_2028826 := by
    simpa [prefixWord, tailWord_2028826, baseEnd_2028826] using wordTrace_append hprefix tailTrace_2028826
  have hstable : (prefixWord ++ tailWord_2028826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028826).length < 2 ^ (prefixWord ++ tailWord_2028826).sum := by decide
  have hdescent : baseEnd_2028826 < baseStart_2028826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028836 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_2028836 : Nat := 118140960795 + 2028836 * 2 ^ 59
def prefixEnd_2028836 : Nat := 4983230072969 + 3 ^ 40 * 2028836 * 2
def baseEnd_2028836 : Nat := 347256012381776467839853

theorem tailTrace_2028836 : CollatzResearch.WordTrace tailWord_2028836 prefixEnd_2028836 347256012381776467839853 := by
  unfold tailWord_2028836
  simp only [CollatzResearch.WordTrace]
  refine ⟨36998864038940572223913181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49331818718587429631884241 36998864038940572223913181)
  ·
    refine ⟨13874574014602714583967443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36998864038940572223913181 13874574014602714583967443)
    ·
      refine ⟨20811861021904071875951165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13874574014602714583967443 20811861021904071875951165)
      ·
        refine ⟨7804447883214026953481687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20811861021904071875951165 7804447883214026953481687)
        ·
          refine ⟨11706671824821040430222531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7804447883214026953481687 11706671824821040430222531)
          ·
            refine ⟨17560007737231560645333797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11706671824821040430222531 17560007737231560645333797)
            ·
              refine ⟨3292501450730917621000087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17560007737231560645333797 3292501450730917621000087)
              ·
                refine ⟨4938752176096376431500131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292501450730917621000087 4938752176096376431500131)
                ·
                  refine ⟨7408128264144564647250197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4938752176096376431500131 7408128264144564647250197)
                  ·
                    refine ⟨347256012381776467839853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7408128264144564647250197 347256012381776467839853)
                    ·
                      rfl

theorem cell23_2028836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_2028836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028836 prefixEnd_2028836 := by exact prefixLift 2028836
  have htrace : WordTrace (prefixWord ++ tailWord_2028836) baseStart_2028836 baseEnd_2028836 := by
    simpa [prefixWord, tailWord_2028836, baseEnd_2028836] using wordTrace_append hprefix tailTrace_2028836
  have hstable : (prefixWord ++ tailWord_2028836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028836).length < 2 ^ (prefixWord ++ tailWord_2028836).sum := by decide
  have hdescent : baseEnd_2028836 < baseStart_2028836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028857 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 1, 5]
def baseStart_2028857 : Nat := 118140960795 + 2028857 * 2 ^ 59
def prefixEnd_2028857 : Nat := 4983230072969 + 3 ^ 40 * 2028857 * 2
def baseEnd_2028857 : Nat := 347259606746357940452321

theorem tailTrace_2028857 : CollatzResearch.WordTrace tailWord_2028857 prefixEnd_2028857 347259606746357940452321 := by
  unfold tailWord_2028857
  simp only [CollatzResearch.WordTrace]
  refine ⟨73998494010805065034340825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49332329340536710022893883 73998494010805065034340825)
  ·
    refine ⟨55498870508103798775755619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73998494010805065034340825 55498870508103798775755619)
    ·
      refine ⟨83248305762155698163633429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55498870508103798775755619 83248305762155698163633429)
      ·
        refine ⟨3902264332601048351420317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83248305762155698163633429 3902264332601048351420317)
        ·
          refine ⟨1463349124725393131782619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3902264332601048351420317 1463349124725393131782619)
          ·
            refine ⟨2195023687088089697673929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463349124725393131782619 2195023687088089697673929)
            ·
              refine ⟨1646267765316067273255447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2195023687088089697673929 1646267765316067273255447)
              ·
                refine ⟨2469401647974100909883171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646267765316067273255447 2469401647974100909883171)
                ·
                  refine ⟨3704102471961151364824757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469401647974100909883171 3704102471961151364824757)
                  ·
                    refine ⟨347259606746357940452321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3704102471961151364824757 347259606746357940452321)
                    ·
                      rfl

theorem cell23_2028857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 1, 5].length) (baseStart_2028857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028857 prefixEnd_2028857 := by exact prefixLift 2028857
  have htrace : WordTrace (prefixWord ++ tailWord_2028857) baseStart_2028857 baseEnd_2028857 := by
    simpa [prefixWord, tailWord_2028857, baseEnd_2028857] using wordTrace_append hprefix tailTrace_2028857
  have hstable : (prefixWord ++ tailWord_2028857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028857).length < 2 ^ (prefixWord ++ tailWord_2028857).sum := by decide
  have hdescent : baseEnd_2028857 < baseStart_2028857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028859 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 3]
def baseStart_2028859 : Nat := 118140960795 + 2028859 * 2 ^ 59
def prefixEnd_2028859 : Nat := 4983230072969 + 3 ^ 40 * 2028859 * 2
def baseEnd_2028859 : Nat := 1041779847200382813531953

theorem tailTrace_2028859 : CollatzResearch.WordTrace tailWord_2028859 prefixEnd_2028859 1041779847200382813531953 := by
  unfold tailWord_2028859
  simp only [CollatzResearch.WordTrace]
  refine ⟨73998566956797819375913631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49332377971198546250609087 73998566956797819375913631)
  ·
    refine ⟨110997850435196729063870447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73998566956797819375913631 110997850435196729063870447)
    ·
      refine ⟨166496775652795093595805671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110997850435196729063870447 166496775652795093595805671)
      ·
        refine ⟨249745163479192640393708507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166496775652795093595805671 249745163479192640393708507)
        ·
          refine ⟨374617745218788960590562761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249745163479192640393708507 374617745218788960590562761)
          ·
            refine ⟨280963308914091720442922071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374617745218788960590562761 280963308914091720442922071)
            ·
              refine ⟨421444963371137580664383107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280963308914091720442922071 421444963371137580664383107)
              ·
                refine ⟨632167445056706370996574661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421444963371137580664383107 632167445056706370996574661)
                ·
                  refine ⟨118531395948132444561857749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 632167445056706370996574661 118531395948132444561857749)
                  ·
                    refine ⟨2778079592534354169418541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118531395948132444561857749 2778079592534354169418541)
                    ·
                      refine ⟨1041779847200382813531953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778079592534354169418541 1041779847200382813531953)
                      ·
                        rfl

theorem cell23_2028859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 3].length) (baseStart_2028859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028859 prefixEnd_2028859 := by exact prefixLift 2028859
  have htrace : WordTrace (prefixWord ++ tailWord_2028859) baseStart_2028859 baseEnd_2028859 := by
    simpa [prefixWord, tailWord_2028859, baseEnd_2028859] using wordTrace_append hprefix tailTrace_2028859
  have hstable : (prefixWord ++ tailWord_2028859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028859).length < 2 ^ (prefixWord ++ tailWord_2028859).sum := by decide
  have hdescent : baseEnd_2028859 < baseStart_2028859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028860 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_2028860 : Nat := 118140960795 + 2028860 * 2 ^ 59
def prefixEnd_2028860 : Nat := 4983230072969 + 3 ^ 40 * 2028860 * 2
def baseEnd_2028860 : Nat := 1041780360681037309619449

theorem tailTrace_2028860 : CollatzResearch.WordTrace tailWord_2028860 prefixEnd_2028860 1041780360681037309619449 := by
  unfold tailWord_2028860
  simp only [CollatzResearch.WordTrace]
  refine ⟨36999301714897098273350017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49332402286529464364466689 36999301714897098273350017)
  ·
    refine ⟨27749476286172823705012513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36999301714897098273350017 27749476286172823705012513)
    ·
      refine ⟨20812107214629617778759385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27749476286172823705012513 20812107214629617778759385)
      ·
        refine ⟨15609080410972213334069539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20812107214629617778759385 15609080410972213334069539)
        ·
          refine ⟨23413620616458320001104309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15609080410972213334069539 23413620616458320001104309)
          ·
            refine ⟨2195026932792967500103529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23413620616458320001104309 2195026932792967500103529)
            ·
              refine ⟨1646270199594725625077647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2195026932792967500103529 1646270199594725625077647)
              ·
                refine ⟨2469405299392088437616471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646270199594725625077647 2469405299392088437616471)
                ·
                  refine ⟨3704107949088132656424707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469405299392088437616471 3704107949088132656424707)
                  ·
                    refine ⟨5556161923632198984637061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3704107949088132656424707 5556161923632198984637061)
                    ·
                      refine ⟨1041780360681037309619449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5556161923632198984637061 1041780360681037309619449)
                      ·
                        rfl

theorem cell23_2028860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_2028860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028860 prefixEnd_2028860 := by exact prefixLift 2028860
  have htrace : WordTrace (prefixWord ++ tailWord_2028860) baseStart_2028860 baseEnd_2028860 := by
    simpa [prefixWord, tailWord_2028860, baseEnd_2028860] using wordTrace_append hprefix tailTrace_2028860
  have hstable : (prefixWord ++ tailWord_2028860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028860).length < 2 ^ (prefixWord ++ tailWord_2028860).sum := by decide
  have hdescent : baseEnd_2028860 < baseStart_2028860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028863 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 3]
def baseStart_2028863 : Nat := 118140960795 + 2028863 * 2 ^ 59
def prefixEnd_2028863 : Nat := 4983230072969 + 3 ^ 40 * 2028863 * 2
def baseEnd_2028863 : Nat := 1041781901123000797881935

theorem tailTrace_2028863 : CollatzResearch.WordTrace tailWord_2028863 prefixEnd_2028863 1041781901123000797881935 := by
  unfold tailWord_2028863
  simp only [CollatzResearch.WordTrace]
  refine ⟨73998712848783328059059243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49332475232522218706039495 73998712848783328059059243)
  ·
    refine ⟨110998069273174992088588865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73998712848783328059059243 110998069273174992088588865)
    ·
      refine ⟨83248551954881244066441649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110998069273174992088588865 83248551954881244066441649)
      ·
        refine ⟨62436413966160933049831237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83248551954881244066441649 62436413966160933049831237)
        ·
          refine ⟨11706827618655174946843357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62436413966160933049831237 11706827618655174946843357)
          ·
            refine ⟨4390060356995690605066259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11706827618655174946843357 4390060356995690605066259)
            ·
              refine ⟨6585090535493535907599389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390060356995690605066259 6585090535493535907599389)
              ·
                refine ⟨2469408950810075965349771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6585090535493535907599389 2469408950810075965349771)
                ·
                  refine ⟨3704113426215113948024657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469408950810075965349771 3704113426215113948024657)
                  ·
                    refine ⟨2778085069661335461018493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3704113426215113948024657 2778085069661335461018493)
                    ·
                      refine ⟨1041781901123000797881935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778085069661335461018493 1041781901123000797881935)
                      ·
                        rfl

theorem cell23_2028863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_2028863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028863 prefixEnd_2028863 := by exact prefixLift 2028863
  have htrace : WordTrace (prefixWord ++ tailWord_2028863) baseStart_2028863 baseEnd_2028863 := by
    simpa [prefixWord, tailWord_2028863, baseEnd_2028863] using wordTrace_append hprefix tailTrace_2028863
  have hstable : (prefixWord ++ tailWord_2028863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028863).length < 2 ^ (prefixWord ++ tailWord_2028863).sum := by decide
  have hdescent : baseEnd_2028863 < baseStart_2028863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2028994 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2028994 : Nat := 118140960795 + 2028994 * 2 ^ 59
def prefixEnd_2028994 : Nat := 4983230072969 + 3 ^ 40 * 2028994 * 2
def baseEnd_2028994 : Nat := 347283055696246595114611

theorem tailTrace_2028994 : CollatzResearch.WordTrace tailWord_2028994 prefixEnd_2028994 347283055696246595114611 := by
  unfold tailWord_2028994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18500872702827184358019509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49335660540872491621385357 18500872702827184358019509)
  ·
    refine ⟨1734456815890048533564329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18500872702827184358019509 1734456815890048533564329)
    ·
      refine ⟨1300842611917536400173247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1734456815890048533564329 1300842611917536400173247)
      ·
        refine ⟨1951263917876304600259871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300842611917536400173247 1951263917876304600259871)
        ·
          refine ⟨2926895876814456900389807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951263917876304600259871 2926895876814456900389807)
          ·
            refine ⟨4390343815221685350584711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926895876814456900389807 4390343815221685350584711)
            ·
              refine ⟨6585515722832528025877067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390343815221685350584711 6585515722832528025877067)
              ·
                refine ⟨9878273584248792038815601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585515722832528025877067 9878273584248792038815601)
                ·
                  refine ⟨7408705188186594029111701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9878273584248792038815601 7408705188186594029111701)
                  ·
                    refine ⟨347283055696246595114611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7408705188186594029111701 347283055696246595114611)
                    ·
                      rfl

theorem cell23_2028994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2028994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2028994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2028994 prefixEnd_2028994 := by exact prefixLift 2028994
  have htrace : WordTrace (prefixWord ++ tailWord_2028994) baseStart_2028994 baseEnd_2028994 := by
    simpa [prefixWord, tailWord_2028994, baseEnd_2028994] using wordTrace_append hprefix tailTrace_2028994
  have hstable : (prefixWord ++ tailWord_2028994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2028994).length < 2 ^ (prefixWord ++ tailWord_2028994).sum := by decide
  have hdescent : baseEnd_2028994 < baseStart_2028994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2028994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029023 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 1, 6, 2]
def baseStart_2029023 : Nat := 118140960795 + 2029023 * 2 ^ 59
def prefixEnd_2029023 : Nat := 4983230072969 + 3 ^ 40 * 2029023 * 2
def baseEnd_2029023 : Nat := 1041864058027720171881199

theorem tailTrace_2029023 : CollatzResearch.WordTrace tailWord_2029023 prefixEnd_2029023 1041864058027720171881199 := by
  unfold tailWord_2029023
  simp only [CollatzResearch.WordTrace]
  refine ⟨74004548528203675384883723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49336365685469116923255815 74004548528203675384883723)
  ·
    refine ⟨111006822792305513077325585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74004548528203675384883723 111006822792305513077325585)
    ·
      refine ⟨83255117094229134807994189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111006822792305513077325585 83255117094229134807994189)
      ·
        refine ⟨31220668910335925552997821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83255117094229134807994189 31220668910335925552997821)
        ·
          refine ⟨11707750841375972082374183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31220668910335925552997821 11707750841375972082374183)
          ·
            refine ⟨17561626262063958123561275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11707750841375972082374183 17561626262063958123561275)
            ·
              refine ⟨26342439393095937185341913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17561626262063958123561275 26342439393095937185341913)
              ·
                refine ⟨19756829544821952889006435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26342439393095937185341913 19756829544821952889006435)
                ·
                  refine ⟨29635244317232929333509653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19756829544821952889006435 29635244317232929333509653)
                  ·
                    refine ⟨1389152077370293562508265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29635244317232929333509653 1389152077370293562508265)
                    ·
                      refine ⟨1041864058027720171881199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1389152077370293562508265 1041864058027720171881199)
                      ·
                        rfl

theorem cell23_2029023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_2029023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029023 prefixEnd_2029023 := by exact prefixLift 2029023
  have htrace : WordTrace (prefixWord ++ tailWord_2029023) baseStart_2029023 baseEnd_2029023 := by
    simpa [prefixWord, tailWord_2029023, baseEnd_2029023] using wordTrace_append hprefix tailTrace_2029023
  have hstable : (prefixWord ++ tailWord_2029023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029023).length < 2 ^ (prefixWord ++ tailWord_2029023).sum := by decide
  have hdescent : baseEnd_2029023 < baseStart_2029023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029050 : List Nat := [3, 1, 1, 1, 1, 2, 3, 6, 1, 4]
def baseStart_2029050 : Nat := 118140960795 + 2029050 * 2 ^ 59
def prefixEnd_2029050 : Nat := 4983230072969 + 3 ^ 40 * 2029050 * 2
def baseEnd_2029050 : Nat := 347292640668463855414525

theorem tailTrace_2029050 : CollatzResearch.WordTrace tailWord_2029050 prefixEnd_2029050 347292640668463855414525 := by
  unfold tailWord_2029050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501383324776464749029151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49337022199403905997411069 18501383324776464749029151)
  ·
    refine ⟨27752074987164697123543727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18501383324776464749029151 27752074987164697123543727)
    ·
      refine ⟨41628112480747045685315591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27752074987164697123543727 41628112480747045685315591)
      ·
        refine ⟨62442168721120568527973387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41628112480747045685315591 62442168721120568527973387)
        ·
          refine ⟨93663253081680852791960081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62442168721120568527973387 93663253081680852791960081)
          ·
            refine ⟨70247439811260639593970061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93663253081680852791960081 70247439811260639593970061)
            ·
              refine ⟨26342789929222739847738773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70247439811260639593970061 26342789929222739847738773)
              ·
                refine ⟨1234818277932315930362755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26342789929222739847738773 1234818277932315930362755)
                ·
                  refine ⟨1852227416898473895544133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1234818277932315930362755 1852227416898473895544133)
                  ·
                    refine ⟨347292640668463855414525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1852227416898473895544133 347292640668463855414525)
                    ·
                      rfl

theorem cell23_2029050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_2029050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029050 prefixEnd_2029050 := by exact prefixLift 2029050
  have htrace : WordTrace (prefixWord ++ tailWord_2029050) baseStart_2029050 baseEnd_2029050 := by
    simpa [prefixWord, tailWord_2029050, baseEnd_2029050] using wordTrace_append hprefix tailTrace_2029050
  have hstable : (prefixWord ++ tailWord_2029050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029050).length < 2 ^ (prefixWord ++ tailWord_2029050).sum := by decide
  have hdescent : baseEnd_2029050 < baseStart_2029050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2029090 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2029090 : Nat := 118140960795 + 2029090 * 2 ^ 59
def prefixEnd_2029090 : Nat := 4983230072969 + 3 ^ 40 * 2029090 * 2
def baseEnd_2029090 : Nat := 1041898461231571409743391

theorem tailTrace_2029090 : CollatzResearch.WordTrace tailWord_2029090 prefixEnd_2029090 1041898461231571409743391 := by
  unfold tailWord_2029090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501748054740236456893181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49337994812640630551715149 18501748054740236456893181)
  ·
    refine ⟨6938155520527588671334943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18501748054740236456893181 6938155520527588671334943)
    ·
      refine ⟨10407233280791383007002415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938155520527588671334943 10407233280791383007002415)
      ·
        refine ⟨15610849921187074510503623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10407233280791383007002415 15610849921187074510503623)
        ·
          refine ⟨23416274881780611765755435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610849921187074510503623 23416274881780611765755435)
          ·
            refine ⟨35124412322670917648633153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23416274881780611765755435 35124412322670917648633153)
            ·
              refine ⟨26343309242003188236474865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35124412322670917648633153 26343309242003188236474865)
              ·
                refine ⟨19757481931502391177356149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26343309242003188236474865 19757481931502391177356149)
                ·
                  refine ⟨1852263931078349172877139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19757481931502391177356149 1852263931078349172877139)
                  ·
                    refine ⟨2778395896617523759315709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1852263931078349172877139 2778395896617523759315709)
                    ·
                      refine ⟨1041898461231571409743391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2778395896617523759315709 1041898461231571409743391)
                      ·
                        rfl

theorem cell23_2029090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2029090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2029090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2029090 prefixEnd_2029090 := by exact prefixLift 2029090
  have htrace : WordTrace (prefixWord ++ tailWord_2029090) baseStart_2029090 baseEnd_2029090 := by
    simpa [prefixWord, tailWord_2029090, baseEnd_2029090] using wordTrace_append hprefix tailTrace_2029090
  have hstable : (prefixWord ++ tailWord_2029090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2029090).length < 2 ^ (prefixWord ++ tailWord_2029090).sum := by decide
  have hdescent : baseEnd_2029090 < baseStart_2029090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2029090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
